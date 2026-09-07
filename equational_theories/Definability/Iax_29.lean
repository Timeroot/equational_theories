import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq82 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq82 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq82 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq86 (σ X0) (σ X1)
       grind)
    | exact superpose eq86 eq13
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq102
    | exact resolve eq102 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq102
  have eq932 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq107 x y
       grind)
    | exact superpose eq107 eq14
    | (have r₁ := eq14
       have r₂ := eq107 x y
       grind)
    | exact resolve eq14 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq956 : False := by grind
  exact eq956

/-- `Equation4460`: `x ◇ (y ◇ x) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4460 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4460 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X0) := by
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
  have eq20 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
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
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    grind
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = (M.op (M.op X3 X3) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq20 X2 (M.op X1 (M.op X2 X2)) X0
       grind)
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq20 X0 (M.op X1 (M.op X2 X2)) X2
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq75 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq157 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq143 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq143
    | exact resolve eq143 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq368 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq157 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq157 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq157
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq157 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq682 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq694 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq157
    | (have j1 := eq33 X1 X0
       grind)
    | exact resolve eq157 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq717 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq694
    | (have j0 := eq694 X0 X1
       grind)
    | exact resolve eq694 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq1860 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1936 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq10
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1964 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1860 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1860
    | (have j0 := eq1860 X0 X1
       grind)
    | exact resolve eq1860 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860
  have eq2030 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq3887 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq128 X0 X0
       grind)
    | exact superpose eq128 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq128 X0 X0
       grind)
    | exact resolve eq12 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq6512 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq660
       have i₂ := eq2030 y x
       grind)
    | exact superpose eq2030 eq660
    | (have j1 := eq2030 y x
       grind)
    | (have r₁ := eq660
       have r₂ := eq2030 y x
       grind)
    | exact resolve eq660 eq2030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030
  have eq6513 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq660
       have i₂ := eq1964 y x
       grind)
    | exact superpose eq1964 eq660
    | (have j1 := eq1964 (σ y) (σ x)
       grind)
    | (have r₁ := eq660
       have r₂ := eq1964 y x
       grind)
    | exact resolve eq660 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq6514 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq6513
  have eq6515 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq6512
  have eq6525 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq157 x
       have i₂ := eq6514
       grind)
    | exact superpose eq6514 eq157
    | exact resolve eq157 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6584 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6525
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6525
    | exact resolve eq6525 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6525
  have eq6679 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6584
       grind)
    | exact superpose eq6584 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6682 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1964 y x
       have i₂ := eq6584
       grind)
    | exact superpose eq6584 eq1964
    | (have j0 := eq1964 y x
       grind)
    | exact resolve eq1964 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964 eq6584
  have eq6683 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq6682
  have eq6684 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq6679
  have eq8276 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq682 x x
       have i₂ := eq6514
       grind)
    | exact superpose eq6514 eq682
    | exact resolve eq682 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq8340 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8276
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8276
    | exact resolve eq8276 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8276
  have eq8356 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq157 x
       have i₂ := eq6515
       grind)
    | exact superpose eq6515 eq157
    | exact resolve eq157 eq6515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq6515
  have eq8425 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq8356
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8356
    | exact resolve eq8356 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8356
  have eq8426 : x = (k x y) := by grind
  clear eq8425
  have eq15907 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq368 (σ X1) X0
       grind)
    | exact superpose eq368 eq26
    | (have j1 := eq368 (σ X1) X0
       grind)
    | exact resolve eq26 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq368
  have eq15937 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15907 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15907
    | (have j0 := eq15907 X0 X1
       grind)
    | exact resolve eq15907 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15907
  have eq15973 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15937 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq15937
    | (have j0 := eq15937 X0 X1
       grind)
    | exact resolve eq15937 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15937
  have eq27926 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq8340
       grind)
    | exact superpose eq8340 eq9
    | exact resolve eq9 eq8340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8340
  have eq27982 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq27926
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq27926
    | exact resolve eq27926 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27926
  have eq28763 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31 x x
       have i₂ := eq27982
       grind)
    | exact superpose eq27982 eq31
    | exact resolve eq31 eq27982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq27982
  have eq28771 : y = (M.op x x) ∨ x = y := by grind
  clear eq28763
  have eq29935 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq28771
       grind)
    | exact superpose eq28771 eq8
    | exact resolve eq8 eq28771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31299 : (M.op x y) = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq29935 x x
       have i₂ := eq28771
       grind)
    | exact superpose eq28771 eq29935
    | exact resolve eq29935 eq28771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28771
  have eq31534 : (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq31299
  have eq32734 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq29935 x y
       have i₂ := eq31534
       grind)
    | exact superpose eq31534 eq29935
    | exact resolve eq29935 eq31534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29935 eq31534
  have eq32735 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq32734
  have eq39240 : x ≠ (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq135 x (M.op x y)
       have i₂ := eq32735
       grind)
    | exact superpose eq32735 eq135
    | (have j0 := eq135 x y
       grind)
    | exact resolve eq135 eq32735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32735
  have eq83750 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15973 x x
       have i₂ := eq6514
       grind)
    | exact superpose eq6514 eq15973
    | (have j0 := eq15973 x x
       grind)
    | exact resolve eq15973 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15973
  have eq83835 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83750
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq83750
    | exact resolve eq83750 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83750
  have eq96260 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq83835
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq83835
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq83835 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83835
  have eq96327 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq96260
  have eq98142 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq135 x x
       have i₂ := eq96327
       grind)
    | exact superpose eq96327 eq135
    | (have j0 := eq135 x x
       grind)
    | (have r₁ := eq135 x x
       have r₂ := eq96327
       grind)
    | exact resolve eq135 eq96327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98189 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq96327
  have eq98190 : x ≠ y ∨ x = (k x x) := by
    first
    | (have j1 := eq135 x x
       grind)
    | (have r₁ := eq98142
       have r₂ := eq135 x x
       grind)
    | exact resolve eq98142 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq98142
  have eq168612 : x ≠ x ∨ x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39240
       have i₂ := eq6684
       grind)
    | exact superpose eq6684 eq39240
    | (have r₁ := eq39240
       have r₂ := eq6684
       grind)
    | exact resolve eq39240 eq6684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6684 eq39240
  have eq168613 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq168612
  have eq168614 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq168613
       have r₂ := eq98190
       grind)
    | exact resolve eq168613 eq98190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98190 eq168613
  have eq169516 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq713 x
       have i₂ := eq168614
       grind)
    | exact superpose eq168614 eq713
    | (have j0 := eq713 x
       grind)
    | exact resolve eq713 eq168614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168614
  have eq169543 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq169516
  have eq173734 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6514
       have i₂ := eq169543
       grind)
    | exact superpose eq169543 eq6514
    | exact resolve eq6514 eq169543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173745 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (σ x)
       have i₂ := eq169543
       grind)
    | exact superpose eq169543 eq8
    | exact resolve eq8 eq169543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169543
  have eq173868 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq173734
  have eq243951 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq173745 (σ x) (σ x)
       have i₂ := eq6514
       grind)
    | exact superpose eq6514 eq173745
    | exact resolve eq173745 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514 eq173745
  have eq244137 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq243951
  have eq246169 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq244137
       grind)
    | exact superpose eq244137 eq14
    | exact resolve eq14 eq244137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244137
  have eq249412 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq246169
       have i₂ := eq6683
       grind)
    | exact superpose eq6683 eq246169
    | exact resolve eq246169 eq6683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6683 eq246169
  have eq249413 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq249412
  have eq249415 : y = (M.op x x) := by
    first
    | (have r₁ := eq249413
       have r₂ := eq173868
       grind)
    | exact resolve eq249413 eq173868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173868 eq249413
  have eq252362 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq8
    | exact resolve eq8 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252366 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 x
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq20
    | exact resolve eq20 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq252376 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq69 x X0
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq69
    | exact resolve eq69 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq252378 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) y) = (M.op (M.op X0 X0) (M.op X1 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X1 x x
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq71
    | exact resolve eq71 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq254775 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op y (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq252362 (σ X1) (σ X0)
       have i₂ := eq717 X1 X0
       grind)
    | exact superpose eq717 eq252362
    | (have j1 := eq717 X1 X0
       grind)
    | exact resolve eq252362 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq254801 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq252362 x x
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq252362
    | exact resolve eq252362 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258401 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq258492 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq258401 X0 X1
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq258401
    | (have j0 := eq258401 X0 X1
       grind)
    | exact resolve eq258401 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258401
  have eq261262 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (τ X1))
       have i₂ := eq1936 X0 X1
       grind)
    | exact superpose eq1936 eq9
    | (have j1 := eq1936 X0 X1
       grind)
    | exact resolve eq9 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261267 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1936 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq261268 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq261267 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq261267
    | (have j0 := eq261267 X0
       grind)
    | exact resolve eq261267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261267
  have eq261273 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq261262 X0 X1
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq261262
    | (have j0 := eq261262 X0 X1
       grind)
    | exact resolve eq261262 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq261262
  have eq279852 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq252376 y
       have i₂ := eq252362 y y
       grind)
    | exact superpose eq252362 eq252376
    | exact resolve eq252376 eq252362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252362 eq252376
  have eq279966 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) := by
    first
    | (have i₁ := eq261268 (M.op y y)
       have i₂ := eq279852
       grind)
    | exact superpose eq279852 eq261268
    | (have j0 := eq261268 (M.op y y)
       grind)
    | (have r₁ := eq261268 (M.op y y)
       have r₂ := eq279852
       grind)
    | exact resolve eq261268 eq279852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261268 eq279852
  have eq279971 : (M.op y y) = (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) := by grind
  clear eq279966
  have eq296355 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = X0 ∨ (τ (k (M.op y y) X0)) = (τ (M.op (M.op y y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq252378 y y X1
       have i₂ := eq258492 X0 (M.op y y)
       grind)
    | (have i₁ := eq252378 X0 X1 x
       have i₂ := eq258492 (M.op (M.op X0 X0) (M.op X1 y)) X1
       grind)
    | exact superpose eq258492 eq252378
    | (have j1 := eq258492 X0 (M.op y y)
       grind)
    | exact resolve eq252378 eq258492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252378 eq258492
  have eq296389 : ∀ X0 : G, (M.op y y) = X0 ∨ (τ (k (M.op y y) X0)) = (τ (M.op (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq296355 X0 x
       have i₂ := eq252366 x y
       grind)
    | exact superpose eq252366 eq296355
    | (have j0 := eq296355 X0 x
       grind)
    | exact resolve eq296355 eq252366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296355
  have eq296468 : ∀ X0 : G, (τ (M.op y X0)) = (τ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq296389 X0
       have i₂ := eq252366 y X0
       grind)
    | exact superpose eq252366 eq296389
    | (have j0 := eq296389 X0
       grind)
    | exact resolve eq296389 eq252366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296389
  have eq317270 : (τ (M.op y y)) = (M.op (τ (M.op y y)) (τ (M.op y y))) := by
    first
    | (have i₁ := eq9 (M.op (τ (M.op y y)) (τ (M.op y y)))
       have i₂ := eq279971
       grind)
    | exact superpose eq279971 eq9
    | exact resolve eq9 eq279971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319331 : ∀ X0 : G, (M.op y X0) = (M.op (τ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq252366 (τ (M.op y y)) X0
       have i₂ := eq317270
       grind)
    | exact superpose eq317270 eq252366
    | exact resolve eq252366 eq317270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252366
  have eq324706 : ∀ X0 : G, (M.op y y) = X0 ∨ (M.op (τ (M.op y y)) (τ X0)) = (k (τ (M.op y y)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq279971
       have i₂ := eq261273 (τ (M.op y y)) X0
       grind)
    | (have i₁ := eq279971
       have i₂ := eq261273 X0 (σ (M.op (τ (M.op y y)) (τ (M.op y y))))
       grind)
    | exact superpose eq261273 eq279971
    | (have j1 := eq261273 (τ (M.op y y)) X0
       grind)
    | exact resolve eq279971 eq261273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261273 eq279971
  have eq324717 : ∀ X0 : G, (τ (k (M.op y y) X0)) = (M.op (τ (M.op y y)) (τ X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq324706 X0
       have i₂ := eq72 X0 (M.op y y)
       grind)
    | exact superpose eq72 eq324706
    | (have j0 := eq324706 X0
       grind)
    | exact resolve eq324706 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq324706
  have eq324730 : ∀ X0 : G, (M.op y (τ X0)) = (τ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq324717 X0
       have i₂ := eq319331 (τ X0)
       grind)
    | exact superpose eq319331 eq324717
    | (have j0 := eq324717 X0
       grind)
    | exact resolve eq324717 eq319331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319331 eq324717
  have eq434994 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3887 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq434995 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq434994 X0 X1
       have j1 := eq645 X1 X0
       grind)
    | (have r₁ := eq434994 (k X1 X1) X0
       have r₂ := eq645 X0 X1
       grind)
    | (have r₁ := eq434994 X0 (σ (k X1 X1))
       have r₂ := eq645 (σ X0) X1
       grind)
    | (have r₁ := eq434994 X1 X0
       have r₂ := eq645 X0 X1
       grind)
    | exact resolve eq434994 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq434994
  have eq435017 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq434995 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq434995 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq434995 eq16
    | (have j1 := eq434995 (τ X1) X0
       grind)
    | exact resolve eq16 eq434995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq435018 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq434995 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq434995 X0 (σ X0)
       grind)
    | exact superpose eq434995 eq9
    | (have j1 := eq434995 X1 X0
       grind)
    | exact resolve eq9 eq434995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434995
  have eq435029 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq435017 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq435017
    | (have j0 := eq435017 X0 X1
       grind)
    | exact resolve eq435017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435017
  have eq435035 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq435029 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq435029
    | (have j0 := eq435029 X0 X1
       grind)
    | exact resolve eq435029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435029
  have eq435183 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq435035 (τ X1) X0
       grind)
    | exact superpose eq435035 eq17
    | (have j1 := eq435035 (τ X1) X0
       grind)
    | exact resolve eq17 eq435035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq435035
  have eq435475 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq435018 (σ X1) X0
       grind)
    | exact superpose eq435018 eq13
    | (have j1 := eq435018 (σ X1) X0
       grind)
    | exact resolve eq13 eq435018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435018
  have eq435480 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq435475 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq435475
    | (have j0 := eq435475 X0 X1
       grind)
    | exact resolve eq435475 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435475
  have eq436287 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq435480 x y
       grind)
    | exact superpose eq435480 eq14
    | (have j1 := eq435480 x y
       grind)
    | exact resolve eq14 eq435480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435480
  have eq436378 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq436287
       have i₂ := eq8426
       grind)
    | exact superpose eq8426 eq436287
    | exact resolve eq436287 eq8426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436287
  have eq455620 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq435183 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq435183
    | exact resolve eq435183 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435183
  have eq455647 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq455620 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq455620
    | (have j0 := eq455620 X0 X1
       grind)
    | exact resolve eq455620 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455620
  have eq455671 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq455647 y x
       have i₂ := eq8426
       grind)
    | exact superpose eq8426 eq455647
    | (have j0 := eq455647 y x
       grind)
    | exact resolve eq455647 eq8426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8426 eq455647
  have eq455779 : y = (k x x) := by
    first
    | (have r₁ := eq455671
       have r₂ := eq436378
       grind)
    | exact resolve eq455671 eq436378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436378 eq455671
  have eq455859 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq713 x
       have i₂ := eq455779
       grind)
    | exact superpose eq455779 eq713
    | (have j0 := eq713 x
       grind)
    | exact resolve eq713 eq455779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq532025 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) ∨ (M.op y y) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq296468 X0
       have i₂ := eq324730 X0
       grind)
    | exact superpose eq324730 eq296468
    | (have j0 := eq296468 X0
       have j1 := eq324730 X0
       grind)
    | exact resolve eq296468 eq324730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296468 eq324730
  have eq532028 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq532025 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532025
  have eq532065 : ∀ X0 : G, (M.op y X0) = (σ (M.op y (τ X0))) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y X0)
       have i₂ := eq532028 X0
       grind)
    | exact superpose eq532028 eq10
    | (have j1 := eq532028 X0
       grind)
    | exact resolve eq10 eq532028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532028
  have eq532108 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ X0)) ∨ (σ X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq532065 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq532065
    | (have j0 := eq532065 (σ X0)
       grind)
    | exact resolve eq532065 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532065
  have eq532646 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq532108 x
       have i₂ := eq254801
       grind)
    | exact superpose eq254801 eq532108
    | (have j0 := eq532108 x
       grind)
    | exact resolve eq532108 eq254801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254801 eq532108
  have eq608343 : (M.op (σ x) (σ y)) = (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq254775 x x
       have i₂ := eq455779
       grind)
    | exact superpose eq455779 eq254775
    | exact resolve eq254775 eq455779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254775 eq455779
  have eq608378 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq608343
       grind)
    | exact superpose eq608343 eq14
    | exact resolve eq14 eq608343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608343
  have eq609195 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq608378
       have i₂ := eq532646
       grind)
    | exact superpose eq532646 eq608378
    | (have r₁ := eq608378
       have r₂ := eq532646
       grind)
    | exact resolve eq608378 eq532646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532646 eq608378
  have eq609197 : (σ x) = (M.op y y) ∨ x = y := by grind
  clear eq609195
  have eq609943 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq317270
       have i₂ := eq609197
       grind)
    | exact superpose eq609197 eq317270
    | exact resolve eq317270 eq609197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317270 eq609197
  have eq610669 : x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq609943
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq609943
    | exact resolve eq609943 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609943
  have eq610741 : x = (M.op x x) := by
    first
    | (have r₁ := eq610669
       have r₂ := eq98189
       grind)
    | exact resolve eq610669 eq98189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98189 eq610669
  have eq610804 : x = y := by
    first
    | (have i₁ := eq249415
       have i₂ := eq610741
       grind)
    | exact superpose eq610741 eq249415
    | exact resolve eq249415 eq610741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610741
  have eq613169 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq610804
       grind)
    | exact superpose eq610804 eq14
    | exact resolve eq14 eq610804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613636 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq455859
       have i₂ := eq610804
       grind)
    | exact superpose eq610804 eq455859
    | exact resolve eq455859 eq610804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455859
  have eq613736 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq613636
  have eq613886 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq613169
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq613169
    | exact resolve eq613169 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249415 eq613169
  have eq614005 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq613886
       have i₂ := eq613736
       grind)
    | exact superpose eq613736 eq613886
    | exact resolve eq613886 eq613736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613736 eq613886
  have eq614043 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq614005
       have i₂ := eq610804
       grind)
    | exact superpose eq610804 eq614005
    | exact resolve eq614005 eq610804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610804 eq614005
  have eq614044 : False := by grind
  exact eq614044

/-- `Equation4460`: `x ◇ (y ◇ x) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation4460 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4460 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X0) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq34 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34
    | exact resolve eq34 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X1 X1)) := by
    intro X0 X1
    grind
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = (M.op (M.op X3 X3) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq20 X2 (M.op X1 (M.op X2 X2)) X0
       grind)
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq20 X0 (M.op X1 (M.op X2 X2)) X2
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25
    | exact resolve eq25 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq82 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq119 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq128 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq29
    | exact resolve eq29 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq43 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq43
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq643 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq680 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
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
  have eq692 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq82
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq82 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq715 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq692
    | (have j0 := eq692 X0 X1
       grind)
    | exact resolve eq692 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq1857 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1933 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq10
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1961 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1857 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1857
    | (have j0 := eq1857 X0 X1
       grind)
    | exact resolve eq1857 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857
  have eq2027 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq3930 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq128 X0 X0
       grind)
    | exact superpose eq128 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq128 X0 X0
       grind)
    | exact resolve eq12 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq4892 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq140 X1 (σ X0)
       grind)
    | exact superpose eq140 eq13
    | (have j1 := eq140 X1 (σ X0)
       grind)
    | exact resolve eq13 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq4932 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4892 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4892
    | (have j0 := eq4892 X0 X1
       grind)
    | exact resolve eq4892 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4892
  have eq6563 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq658
       have i₂ := eq2027 y x
       grind)
    | exact superpose eq2027 eq658
    | (have j1 := eq2027 y x
       grind)
    | (have r₁ := eq658
       have r₂ := eq2027 y x
       grind)
    | exact resolve eq658 eq2027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq6564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq658
       have i₂ := eq1961 y x
       grind)
    | exact superpose eq1961 eq658
    | (have j1 := eq1961 (σ y) (σ x)
       grind)
    | (have r₁ := eq658
       have r₂ := eq1961 y x
       grind)
    | exact resolve eq658 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq6565 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq6564
  have eq6566 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by grind
  clear eq6563
  have eq6576 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82 x
       have i₂ := eq6565
       grind)
    | exact superpose eq6565 eq82
    | exact resolve eq82 eq6565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6633 : x = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6576
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6576
    | exact resolve eq6576 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6576
  have eq6727 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1961 y x
       have i₂ := eq6633
       grind)
    | exact superpose eq6633 eq1961
    | (have j0 := eq1961 y x
       grind)
    | exact resolve eq1961 eq6633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961 eq6633
  have eq6728 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq6727
  have eq8199 : x = (k (τ (σ y)) x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq82 x
       have i₂ := eq6566
       grind)
    | exact superpose eq6566 eq82
    | exact resolve eq82 eq6566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6566
  have eq8264 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq8199
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8199
    | exact resolve eq8199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8199
  have eq8265 : x = (k y x) := by grind
  clear eq8264
  have eq8325 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq680 x x
       have i₂ := eq6565
       grind)
    | exact superpose eq6565 eq680
    | exact resolve eq680 eq6565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq8387 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8325
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8325
    | exact resolve eq8325 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8325
  have eq23757 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq8387
       grind)
    | exact superpose eq8387 eq9
    | exact resolve eq9 eq8387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8387
  have eq23809 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23757
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq23757
    | exact resolve eq23757 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23757
  have eq24752 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29 x x
       have i₂ := eq23809
       grind)
    | exact superpose eq23809 eq29
    | exact resolve eq29 eq23809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23809
  have eq24760 : y = (M.op x x) ∨ x = y := by grind
  clear eq24752
  have eq103262 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq119 (σ x) x
       have i₂ := eq6565
       grind)
    | exact superpose eq6565 eq119
    | exact resolve eq119 eq6565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103297 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq119
    | exact resolve eq119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103997 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1
       have i₂ := eq119 (σ X1) X0
       grind)
    | exact superpose eq119 eq82
    | (have j1 := eq119 (σ X1) X0
       grind)
    | exact resolve eq82 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq119
  have eq104064 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq103997 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq103997
    | (have j0 := eq103997 X0 X1
       grind)
    | exact resolve eq103997 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103997
  have eq104107 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq103297 X0 X1
       have i₂ := eq72 X1 X0
       grind)
    | exact superpose eq72 eq103297
    | (have j0 := eq103297 X0 X1
       grind)
    | exact resolve eq103297 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103297
  have eq104117 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103262
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq103262
    | exact resolve eq103262 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103262
  have eq104156 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104064 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq104064
    | (have j0 := eq104064 X0 X1
       grind)
    | exact resolve eq104064 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104064
  have eq104162 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq104117
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq104117
    | exact resolve eq104117 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104117
  have eq111219 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq104156 x x
       have i₂ := eq6565
       grind)
    | exact superpose eq6565 eq104156
    | (have j0 := eq104156 x x
       grind)
    | exact resolve eq104156 eq6565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104156
  have eq111312 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq111219
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq111219
    | exact resolve eq111219 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111219
  have eq112605 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4932 x x
       have i₂ := eq104162
       grind)
    | exact superpose eq104162 eq4932
    | exact resolve eq4932 eq104162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4932 eq104162
  have eq112610 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq112605
  have eq132481 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq111312
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq111312
    | (have j1 := eq12 y x
       grind)
    | exact resolve eq111312 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132509 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq111312
  have eq132518 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq132481
  have eq132523 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq132509
       have r₂ := eq24760
       grind)
    | exact resolve eq132509 eq24760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24760 eq132509
  have eq134930 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq132518
  have eq139974 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq711 x
       have i₂ := eq132523
       grind)
    | exact superpose eq132523 eq711
    | (have j0 := eq711 x
       grind)
    | exact resolve eq711 eq132523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132523
  have eq139996 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq139974
  have eq145696 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (σ x)
       have i₂ := eq139996
       grind)
    | exact superpose eq139996 eq8
    | exact resolve eq8 eq139996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139996
  have eq208002 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq145696 (σ x) (σ x)
       have i₂ := eq6565
       grind)
    | exact superpose eq6565 eq145696
    | exact resolve eq145696 eq6565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6565 eq145696
  have eq208187 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq208002
  have eq210998 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq208187
       grind)
    | exact superpose eq208187 eq14
    | exact resolve eq14 eq208187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208187
  have eq214060 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq210998
       have i₂ := eq6728
       grind)
    | exact superpose eq6728 eq210998
    | exact resolve eq210998 eq6728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6728 eq210998
  have eq214061 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq214060
  have eq214063 : y = (M.op x x) := by
    first
    | (have r₁ := eq214061
       have r₂ := eq112610
       grind)
    | exact resolve eq214061 eq112610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112610 eq214061
  have eq217305 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq214063
       grind)
    | exact superpose eq214063 eq8
    | exact resolve eq8 eq214063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217309 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 x
       have i₂ := eq214063
       grind)
    | exact superpose eq214063 eq20
    | exact resolve eq20 eq214063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq217320 : ∀ X0 : G, (M.op X0 X0) = (k (M.op y (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 x X0
       have i₂ := eq214063
       grind)
    | exact superpose eq214063 eq69
    | exact resolve eq69 eq214063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq217321 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) y) = (M.op (M.op X0 X0) (M.op X1 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X1 x x
       have i₂ := eq214063
       grind)
    | exact superpose eq214063 eq71
    | exact resolve eq71 eq214063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq220887 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X0 X1))) = (M.op y (σ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq217305 (σ X0) (σ X1)
       have i₂ := eq715 X0 X1
       grind)
    | exact superpose eq715 eq217305
    | (have j1 := eq715 X0 X1
       grind)
    | exact resolve eq217305 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq220917 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq217305 x x
       have i₂ := eq214063
       grind)
    | exact superpose eq214063 eq217305
    | exact resolve eq217305 eq214063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258370 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 (τ X0))
       have i₂ := eq1933 X1 X0
       grind)
    | exact superpose eq1933 eq9
    | (have j1 := eq1933 X1 X0
       grind)
    | exact resolve eq9 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258375 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1933 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933
  have eq258376 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq258375 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq258375
    | (have j0 := eq258375 X0
       grind)
    | exact resolve eq258375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258375
  have eq258381 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq258370 X0 X1
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq258370
    | (have j0 := eq258370 X0 X1
       grind)
    | exact resolve eq258370 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq258370
  have eq266736 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq217320 y
       have i₂ := eq217305 y y
       grind)
    | exact superpose eq217305 eq217320
    | exact resolve eq217320 eq217305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217305 eq217320
  have eq267617 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) := by
    first
    | (have i₁ := eq258376 (M.op y y)
       have i₂ := eq266736
       grind)
    | exact superpose eq266736 eq258376
    | (have j0 := eq258376 (M.op y y)
       grind)
    | (have r₁ := eq258376 (M.op y y)
       have r₂ := eq266736
       grind)
    | exact resolve eq258376 eq266736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258376 eq266736
  have eq267622 : (M.op y y) = (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) := by grind
  clear eq267617
  have eq268518 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = X1 ∨ (τ (k X1 (M.op y y))) = (τ (M.op (M.op y y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104107 X1 (M.op y y)
       have i₂ := eq217321 y y X0
       grind)
    | exact superpose eq217321 eq104107
    | (have j0 := eq104107 X1 (M.op y y)
       grind)
    | exact resolve eq104107 eq217321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104107 eq217321
  have eq268574 : ∀ X1 : G, (M.op y y) = X1 ∨ (τ (k X1 (M.op y y))) = (τ (M.op (M.op y y) X1)) := by
    intro X1
    first
    | (have i₁ := eq268518 x X1
       have i₂ := eq217309 x y
       grind)
    | exact superpose eq217309 eq268518
    | (have j0 := eq268518 x X1
       grind)
    | exact resolve eq268518 eq217309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268518
  have eq269013 : ∀ X1 : G, (τ (M.op y X1)) = (τ (k X1 (M.op y y))) ∨ (M.op y y) = X1 := by
    intro X1
    first
    | (have i₁ := eq268574 X1
       have i₂ := eq217309 y X1
       grind)
    | exact superpose eq217309 eq268574
    | (have j0 := eq268574 X1
       grind)
    | exact resolve eq268574 eq217309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268574
  have eq297707 : (τ (M.op y y)) = (M.op (τ (M.op y y)) (τ (M.op y y))) := by
    first
    | (have i₁ := eq9 (M.op (τ (M.op y y)) (τ (M.op y y)))
       have i₂ := eq267622
       grind)
    | exact superpose eq267622 eq9
    | exact resolve eq9 eq267622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302893 : ∀ X0 : G, (M.op y X0) = (M.op (τ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq217309 (τ (M.op y y)) X0
       have i₂ := eq297707
       grind)
    | exact superpose eq297707 eq217309
    | exact resolve eq217309 eq297707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217309
  have eq314159 : ∀ X0 : G, (M.op y y) = X0 ∨ (M.op (τ (M.op y y)) (τ X0)) = (k (τ X0) (τ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq267622
       have i₂ := eq258381 X0 (τ (M.op y y))
       grind)
    | (have i₁ := eq267622
       have i₂ := eq258381 (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) x
       grind)
    | exact superpose eq258381 eq267622
    | (have j1 := eq258381 X0 (τ (M.op y y))
       grind)
    | exact resolve eq267622 eq258381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258381 eq267622
  have eq314167 : ∀ X0 : G, (τ (k X0 (M.op y y))) = (M.op (τ (M.op y y)) (τ X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq314159 X0
       have i₂ := eq72 (M.op y y) X0
       grind)
    | exact superpose eq72 eq314159
    | (have j0 := eq314159 X0
       grind)
    | exact resolve eq314159 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq314159
  have eq314177 : ∀ X0 : G, (M.op y (τ X0)) = (τ (k X0 (M.op y y))) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq314167 X0
       have i₂ := eq302893 (τ X0)
       grind)
    | exact superpose eq302893 eq314167
    | (have j0 := eq314167 X0
       grind)
    | exact resolve eq314167 eq302893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302893 eq314167
  have eq408461 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3930 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3930
  have eq408462 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq408461 X0 X1
       have j1 := eq643 X1 X0
       grind)
    | (have r₁ := eq408461 (k X1 X1) X0
       have r₂ := eq643 X0 X1
       grind)
    | (have r₁ := eq408461 X0 (σ (k X1 X1))
       have r₂ := eq643 (σ X0) X1
       grind)
    | (have r₁ := eq408461 X1 X0
       have r₂ := eq643 X0 X1
       grind)
    | exact resolve eq408461 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq408461
  have eq408484 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq408462 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq408462 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq408462 eq16
    | (have j1 := eq408462 (τ X1) X0
       grind)
    | exact resolve eq16 eq408462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408485 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq408462 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq408462 X0 (σ X0)
       grind)
    | exact superpose eq408462 eq9
    | (have j1 := eq408462 X1 X0
       grind)
    | exact resolve eq9 eq408462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408462
  have eq408495 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq408484 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq408484
    | (have j0 := eq408484 X0 X1
       grind)
    | exact resolve eq408484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408484
  have eq408501 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq408495 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq408495
    | (have j0 := eq408495 X0 X1
       grind)
    | exact resolve eq408495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408495
  have eq408662 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq408501 (τ X1) X0
       grind)
    | exact superpose eq408501 eq16
    | (have j1 := eq408501 (τ X1) X0
       grind)
    | exact resolve eq16 eq408501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq408501
  have eq408946 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq408485 (σ X1) X0
       grind)
    | exact superpose eq408485 eq13
    | (have j1 := eq408485 (σ X1) X0
       grind)
    | exact resolve eq13 eq408485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408485
  have eq408950 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq408946 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq408946
    | (have j0 := eq408946 X0 X1
       grind)
    | exact resolve eq408946 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408946
  have eq409906 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq408950 x y
       grind)
    | exact superpose eq408950 eq14
    | (have j1 := eq408950 x y
       grind)
    | exact resolve eq14 eq408950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408950
  have eq409996 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq409906
       have i₂ := eq8265
       grind)
    | exact superpose eq8265 eq409906
    | exact resolve eq409906 eq8265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409906
  have eq425206 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq408662 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq408662
    | exact resolve eq408662 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408662
  have eq425230 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq425206 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq425206
    | (have j0 := eq425206 X0 X1
       grind)
    | exact resolve eq425206 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425206
  have eq425269 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq425230 y x
       have i₂ := eq8265
       grind)
    | exact superpose eq8265 eq425230
    | (have j0 := eq425230 y x
       grind)
    | exact resolve eq425230 eq8265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8265 eq425230
  have eq425366 : y = (k x x) := by
    first
    | (have r₁ := eq425269
       have r₂ := eq409996
       grind)
    | exact resolve eq425269 eq409996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409996 eq425269
  have eq425725 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq711 x
       have i₂ := eq425366
       grind)
    | exact superpose eq425366 eq711
    | (have j0 := eq711 x
       grind)
    | exact resolve eq711 eq425366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq499267 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) ∨ (M.op y y) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq269013 X0
       have i₂ := eq314177 X0
       grind)
    | exact superpose eq314177 eq269013
    | (have j0 := eq269013 X0
       have j1 := eq314177 X0
       grind)
    | exact resolve eq269013 eq314177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269013 eq314177
  have eq499270 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq499267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499267
  have eq499299 : ∀ X0 : G, (M.op y X0) = (σ (M.op y (τ X0))) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y X0)
       have i₂ := eq499270 X0
       grind)
    | exact superpose eq499270 eq10
    | (have j1 := eq499270 X0
       grind)
    | exact resolve eq10 eq499270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499270
  have eq499330 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ X0)) ∨ (σ X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq499299 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq499299
    | (have j0 := eq499299 (σ X0)
       grind)
    | exact resolve eq499299 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499299
  have eq499502 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq499330 x
       have i₂ := eq220917
       grind)
    | exact superpose eq220917 eq499330
    | (have j0 := eq499330 x
       grind)
    | exact resolve eq499330 eq220917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220917 eq499330
  have eq555623 : (M.op (σ x) (σ y)) = (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq220887 x x
       have i₂ := eq425366
       grind)
    | exact superpose eq425366 eq220887
    | exact resolve eq220887 eq425366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220887 eq425366
  have eq555738 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq555623
       grind)
    | exact superpose eq555623 eq14
    | exact resolve eq14 eq555623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555623
  have eq555890 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq555738
       have i₂ := eq499502
       grind)
    | exact superpose eq499502 eq555738
    | (have r₁ := eq555738
       have r₂ := eq499502
       grind)
    | exact resolve eq555738 eq499502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499502 eq555738
  have eq555892 : (σ x) = (M.op y y) ∨ x = y := by grind
  clear eq555890
  have eq555911 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq297707
       have i₂ := eq555892
       grind)
    | exact superpose eq555892 eq297707
    | exact resolve eq297707 eq555892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297707 eq555892
  have eq556495 : x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq555911
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq555911
    | exact resolve eq555911 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555911
  have eq556553 : x = (M.op x x) := by
    first
    | (have r₁ := eq556495
       have r₂ := eq134930
       grind)
    | exact resolve eq556495 eq134930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134930 eq556495
  have eq556705 : x = y := by
    first
    | (have i₁ := eq214063
       have i₂ := eq556553
       grind)
    | exact superpose eq556553 eq214063
    | exact resolve eq214063 eq556553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556553
  have eq558599 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq556705
       grind)
    | exact superpose eq556705 eq14
    | exact resolve eq14 eq556705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559063 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq425725
       have i₂ := eq556705
       grind)
    | exact superpose eq556705 eq425725
    | exact resolve eq425725 eq556705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425725
  have eq559152 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq559063
  have eq559294 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq558599
       have i₂ := eq214063
       grind)
    | exact superpose eq214063 eq558599
    | exact resolve eq558599 eq214063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214063 eq558599
  have eq559409 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq559294
       have i₂ := eq559152
       grind)
    | exact superpose eq559152 eq559294
    | exact resolve eq559294 eq559152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559152 eq559294
  have eq559447 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq559409
       have i₂ := eq556705
       grind)
    | exact superpose eq556705 eq559409
    | exact resolve eq559409 eq556705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556705 eq559409
  have eq559448 : False := by grind
  exact eq559448

/-- `Equation4461`: `x ◇ (y ◇ x) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyy_pxy_Equation4461 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4461 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4461.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 x X1 X3
       have i₂ := eq8 x X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq60 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    grind
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (k X0 (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq107 : ∀ X0 X1 : G, (k X1 (M.op X1 X1)) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    grind
  have eq141 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X1 X3) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27 X2 X3 (M.op X1 X3)
       have i₂ := eq8 X3 X1 X0
       grind)
    | exact superpose eq8 eq27
    | exact resolve eq27 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X1 X2 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq27 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27 X2 (M.op X3 X3) X1
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq27
    | exact resolve eq27 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = (M.op (M.op X0 X0) (k X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  clear eq27
  have eq170 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X2 X1
       have i₂ := eq24 X2 X1 X0
       grind)
    | (have i₁ := eq60 X2 X1
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq60
    | exact resolve eq60 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X2 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq60
    | exact resolve eq60 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (k X1 (M.op X1 X1)) = (M.op (k X0 (M.op X0 X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X1 x
       have i₂ := eq63 X0 x (M.op X1 X1)
       grind)
    | exact superpose eq63 eq60
    | exact resolve eq60 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq63
  have eq374 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq640 : ∀ X0 X2 X3 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X3 X3) (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq8 x (M.op X2 X2) X3
       have i₂ := eq170 X2 x X0
       grind)
    | exact superpose eq170 eq8
    | exact resolve eq8 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq689 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X4 (M.op X5 (M.op X4 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq23 X5 X4 x x
       have i₂ := eq23 X1 X0 x x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1717 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 (M.op X0 X0)) = (k (M.op X2 X2) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq374 (M.op x x) (M.op X2 X2)
       have i₂ := eq640 X0 X2 x
       grind)
    | exact superpose eq640 eq374
    | exact resolve eq374 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1719 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq374 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq374
    | exact resolve eq374 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1724 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq374 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq1728 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq1719
  have eq1730 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X0)) = (k (M.op X2 X2) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1717 X0 X1 X2
       grind)
    | (have r₁ := eq1717 X0 X2 X2
       have r₂ := eq640 X0 X2 X2
       grind)
    | exact resolve eq1717 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1958 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1724 (σ X0)
       grind)
    | exact superpose eq1724 eq13
    | exact resolve eq13 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1960 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq1724 (τ X0)
       grind)
    | exact superpose eq1724 eq46
    | exact resolve eq46 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1967 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1960 X0
       have i₂ := eq1724 X0
       grind)
    | exact superpose eq1724 eq1960
    | exact resolve eq1960 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq1969 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1958 X0
       have i₂ := eq1724 X0
       grind)
    | exact superpose eq1724 eq1958
    | exact resolve eq1958 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724 eq1958
  have eq2051 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (τ X0)
       have i₂ := eq1967 X0
       grind)
    | exact superpose eq1967 eq8
    | exact resolve eq8 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2077 : ∀ X0 X1 X2 : G, (k X1 (M.op X1 X1)) = (M.op (M.op X2 X2) (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq640 X1 (τ X0) X2
       have i₂ := eq1967 X0
       grind)
    | exact superpose eq1967 eq640
    | exact resolve eq640 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq1967
  have eq2244 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X0) X1
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq8
    | exact resolve eq8 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2256 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (σ X0)
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq8
    | exact resolve eq8 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2264 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (σ X0)
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq24
    | exact resolve eq24 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2377 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq9
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2455 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2377 X0 X1
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq2377
    | (have j0 := eq2377 X0 X1
       grind)
    | exact resolve eq2377 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq2527 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2455 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq2455
    | (have j0 := eq2455 X0 X1
       grind)
    | exact resolve eq2455 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq3679 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ (σ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2256 (σ X0) X1 X2
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq2256
    | exact resolve eq2256 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq18990 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))) = (M.op (k X2 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232 X0 (M.op X2 X2)
       have i₂ := eq8 X0 (M.op X2 X2) X2
       grind)
    | exact superpose eq8 eq232
    | exact resolve eq232 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq30294 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2527 x y
       grind)
    | exact superpose eq2527 eq14
    | (have j1 := eq2527 x y
       grind)
    | exact resolve eq14 eq2527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq30797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30294
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq30294
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq30294 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30294
  have eq30803 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq30797
  have eq30804 : y = (M.op x x) := by grind
  clear eq30803
  have eq31492 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq8
    | exact resolve eq8 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31493 : (k x y) = (M.op y y) := by grind
  have eq31524 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op y X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141 x X2 X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq141
    | exact resolve eq141 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq31550 : ∀ X0 : G, (k x y) = (k (M.op X0 X0) y) := by
    intro X0
    first
    | (have i₁ := eq1728 x x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq1728
    | exact resolve eq1728 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq31552 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (k y (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1730 X0 X1 x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq1730
    | exact resolve eq1730 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31553 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (k (M.op X1 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq1730 X0 x X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq1730
    | exact resolve eq1730 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31561 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X1 X1) (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2077 x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2077
    | exact resolve eq2077 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq31570 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2244 x X0
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2244
    | exact resolve eq2244 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq31571 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2256 x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2256
    | exact resolve eq2256 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq31572 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2264 x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2264
    | exact resolve eq2264 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq31597 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq145 x x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq145
    | exact resolve eq145 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq31600 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq171 x x X0
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq171
    | exact resolve eq171 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31604 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1 x x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq689
    | exact resolve eq689 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq31621 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq31570 x
       have i₂ := eq31572 x (σ x)
       grind)
    | exact superpose eq31572 eq31570
    | exact resolve eq31570 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31570
  have eq31630 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (σ y) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq31561 X0 x
       have i₂ := eq31572 x (τ y)
       grind)
    | exact superpose eq31572 eq31561
    | exact resolve eq31561 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31561
  have eq31638 : ∀ X1 : G, (k (M.op X1 X1) y) = (M.op x (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq31553 x X1
       have i₂ := eq31600 x
       grind)
    | exact superpose eq31600 eq31553
    | exact resolve eq31553 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31553
  have eq31639 : ∀ X1 : G, (k y (M.op X1 X1)) = (M.op x (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq31552 x X1
       have i₂ := eq31600 x
       grind)
    | exact superpose eq31600 eq31552
    | exact resolve eq31552 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31552
  have eq31661 : ∀ X1 X2 : G, (M.op (M.op X2 X1) (M.op y X2)) = (M.op (σ y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq31524 x X1 X2
       have i₂ := eq31571 x X1
       grind)
    | exact superpose eq31571 eq31524
    | exact resolve eq31524 eq31571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31524
  have eq31700 : (M.op x (M.op x y)) = (M.op (σ y) (τ y)) := by
    first
    | (have i₁ := eq31630 x
       have i₂ := eq31600 x
       grind)
    | exact superpose eq31600 eq31630
    | exact resolve eq31630 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31600 eq31630
  have eq31703 : (k x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq31638 x
       have i₂ := eq31550 x
       grind)
    | exact superpose eq31550 eq31638
    | exact resolve eq31638 eq31550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31550 eq31638
  have eq31743 : (M.op y y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq31703
       have i₂ := eq31493
       grind)
    | exact superpose eq31493 eq31703
    | exact resolve eq31703 eq31493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31493 eq31703
  have eq39575 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X2)) = (M.op (M.op X3 X3) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq146 X3 X2
       have i₂ := eq1730 X3 X1 X0
       grind)
    | (have i₁ := eq146 (M.op X2 X2) X1
       have i₂ := eq1730 X0 (M.op X2 X2) X2
       grind)
    | exact superpose eq1730 eq146
    | exact resolve eq146 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq39862 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (M.op X1 X1) (M.op (k X1 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171 (k X1 (M.op X1 X1)) (M.op X1 X1) X2
       have i₂ := eq146 X1 X0
       grind)
    | exact superpose eq146 eq171
    | exact resolve eq171 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq171
  have eq39887 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (M.op (k X1 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39862 X0 X1 X2
       have i₂ := eq31572 X1 (M.op (k X1 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X0)))
       grind)
    | exact superpose eq31572 eq39862
    | exact resolve eq39862 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39862
  have eq40016 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X2)) = (M.op (σ y) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39575 X0 X1 X2 X3
       have i₂ := eq31572 X3 (k (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq31572 eq39575
    | exact resolve eq39575 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31572 eq39575
  have eq40219 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (k (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39887 X0 X1 X2
       have i₂ := eq18990 X0 X1 X1
       grind)
    | exact superpose eq18990 eq39887
    | exact resolve eq39887 eq18990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18990 eq39887
  have eq40304 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (σ y) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40016 X0 X1 x x
       have i₂ := eq31597 x x
       grind)
    | exact superpose eq31597 eq40016
    | exact resolve eq40016 eq31597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40016
  have eq40480 : ∀ X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (k (M.op X1 X1) (M.op x (M.op x y)))) := by
    intro X1 X2
    first
    | (have i₁ := eq40219 x X1 X2
       have i₂ := eq31597 x X1
       grind)
    | exact superpose eq31597 eq40219
    | exact resolve eq40219 eq31597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31597 eq40219
  have eq40563 : ∀ X0 X1 : G, (M.op y y) = (M.op (σ y) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40304 X0 X1
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq40304
    | exact resolve eq40304 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40304
  have eq40711 : ∀ X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (k (M.op X1 X1) (M.op y y))) := by
    intro X1 X2
    first
    | (have i₁ := eq40480 X1 X2
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq40480
    | exact resolve eq40480 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40480
  have eq40903 : ∀ X2 : G, (k X2 (M.op X2 X2)) = (M.op y y) := by
    intro X2
    first
    | (have i₁ := eq40711 x X2
       have i₂ := eq40563 x y
       grind)
    | exact superpose eq40563 eq40711
    | exact resolve eq40711 eq40563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40563 eq40711
  have eq44369 : ∀ X0 X1 : G, (k X1 X0) = (M.op y y) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40903 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq40903 x
       have i₂ := eq12 X0 (M.op x x)
       grind)
    | exact superpose eq12 eq40903
    | (have j1 := eq12 y (k X1 X0)
       grind)
    | exact resolve eq40903 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40903
  have eq47176 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op y X2) ∨ (M.op X3 X2) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31492 X1 X2
       have i₂ := eq41 X2 X0 X1 X3
       grind)
    | exact superpose eq41 eq31492
    | (have j1 := eq41 X2 X1 X2 X3
       grind)
    | exact resolve eq31492 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq47265 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq31492 x x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq31492
    | exact resolve eq31492 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47391 : ∀ X0 X2 : G, (M.op (τ (M.op X2 X2)) X0) = (M.op y X0) := by
    intro X0 X2
    first
    | (have i₁ := eq2051 X2 x X0
       have i₂ := eq31492 x X0
       grind)
    | exact superpose eq31492 eq2051
    | exact resolve eq2051 eq31492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051
  have eq47396 : ∀ X0 X2 : G, (M.op (σ (σ (M.op X2 X2))) X0) = (M.op y X0) := by
    intro X0 X2
    first
    | (have i₁ := eq3679 X2 x X0
       have i₂ := eq31492 x X0
       grind)
    | exact superpose eq31492 eq3679
    | exact resolve eq3679 eq31492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47459 : ∀ X0 X1 X2 : G, (M.op (σ (σ (M.op X2 X2))) X1) = (M.op (M.op X0 X1) (M.op y X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3679 X2 (M.op X0 X1) X1
       have i₂ := eq31492 X1 X0
       grind)
    | exact superpose eq31492 eq3679
    | exact resolve eq3679 eq31492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3679 eq31492
  have eq47628 : ∀ X1 X2 : G, (M.op (σ (σ (M.op X2 X2))) X1) = (M.op (σ y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq47459 x X1 X2
       have i₂ := eq31661 X1 x
       grind)
    | exact superpose eq31661 eq47459
    | exact resolve eq47459 eq31661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31661 eq47459
  have eq47875 : ∀ X2 X3 : G, (M.op y X2) = (M.op x (M.op x y)) ∨ (M.op X3 X2) = (k X3 X2) := by
    intro X2 X3
    first
    | (have i₁ := eq47176 x x X2 X3
       have i₂ := eq31604 x x
       grind)
    | exact superpose eq31604 eq47176
    | (have j0 := eq47176 x x X2 X3
       grind)
    | exact resolve eq47176 eq31604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31604 eq47176
  have eq47967 : ∀ X1 : G, (M.op y X1) = (M.op (σ y) X1) := by
    intro X1
    first
    | (have i₁ := eq47628 X1 x
       have i₂ := eq47396 X1 x
       grind)
    | exact superpose eq47396 eq47628
    | exact resolve eq47628 eq47396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47396 eq47628
  have eq48141 : ∀ X2 X3 : G, (M.op X3 X2) = (k X3 X2) ∨ (M.op y y) = (M.op y X2) := by
    intro X2 X3
    first
    | (have i₁ := eq47875 X2 X3
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq47875
    | (have j0 := eq47875 X2 X3
       grind)
    | exact resolve eq47875 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47875
  have eq137862 : ∀ X0 : G, (M.op y X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq47391 X0 x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq47391
    | exact resolve eq47391 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30804 eq47391
  have eq139744 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op (τ y) X1)) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 X1 (τ y)
       have i₂ := eq137862 X0
       grind)
    | exact superpose eq137862 eq142
    | exact resolve eq142 eq137862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq139963 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) (τ y)) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq139744 X0 x
       have i₂ := eq31571 x (τ y)
       grind)
    | exact superpose eq31571 eq139744
    | (have j0 := eq139744 X0 x
       grind)
    | exact resolve eq139744 eq31571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31571 eq139744
  have eq140259 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x y)) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq139963 X0
       have i₂ := eq31700
       grind)
    | exact superpose eq31700 eq139963
    | (have j0 := eq139963 X0
       grind)
    | exact resolve eq139963 eq31700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31700 eq139963
  have eq140463 : ∀ X0 : G, (M.op y y) = (M.op y X0) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq140259 X0
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq140259
    | (have j0 := eq140259 X0
       grind)
    | exact resolve eq140259 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140259
  have eq166743 : ∀ X0 X1 : G, (k y X0) = (M.op x (M.op x y)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31639 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq31639 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq31639
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq31639 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31639
  have eq166960 : ∀ X0 X1 : G, (M.op y y) = (k y X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq166743 X0 X1
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq166743
    | (have j0 := eq166743 X0 X1
       grind)
    | exact resolve eq166743 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31743 eq166743
  have eq207742 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq47967 (σ x)
       have i₂ := eq31621
       grind)
    | exact superpose eq31621 eq47967
    | exact resolve eq47967 eq31621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31621 eq47967
  have eq210776 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq207742
       grind)
    | exact superpose eq207742 eq14
    | exact resolve eq14 eq207742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207742
  have eq1159253 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op y y) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44369 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44369
  have eq1229210 : ∀ X0 : G, (M.op y y) ≠ (M.op y X0) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1159253 (τ y) X0
       have i₂ := eq137862 X0
       grind)
    | exact superpose eq137862 eq1159253
    | (have j0 := eq1159253 y X0
       grind)
    | (have r₁ := eq1159253 (τ y) y
       have r₂ := eq137862 y
       grind)
    | exact resolve eq1159253 eq137862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137862 eq1159253
  have eq1229217 : ∀ X0 : G, (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have j0 := eq1229210 X0
       have j1 := eq140463 X0
       grind)
    | (have r₁ := eq1229210 X0
       have r₂ := eq140463 X0
       grind)
    | (have r₁ := eq1229210 y
       have r₂ := eq140463 y
       grind)
    | exact resolve eq1229210 eq140463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140463 eq1229210
  have eq1229258 : ∀ X0 : G, (σ (M.op y X0)) = (k y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq1229217 X0
       grind)
    | exact superpose eq1229217 eq16
    | exact resolve eq16 eq1229217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1229217
  have eq1374660 : ∀ X0 : G, (M.op y y) ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq166960 X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166960
  have eq1374662 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq1374660 X0
       have j1 := eq48141 X0 y
       grind)
    | (have r₁ := eq1374660 x
       have r₂ := eq48141 x x
       grind)
    | (have r₁ := eq1374660 y
       have r₂ := eq48141 y x
       grind)
    | exact resolve eq1374660 eq48141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48141 eq1374660
  have eq1374723 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1229258 X0
       have i₂ := eq1374662 (σ X0)
       grind)
    | exact superpose eq1374662 eq1229258
    | exact resolve eq1229258 eq1374662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229258 eq1374662
  have eq1382749 : (σ (M.op x y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq1374723 x
       have i₂ := eq47265
       grind)
    | exact superpose eq47265 eq1374723
    | exact resolve eq1374723 eq47265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47265 eq1374723
  have eq1382928 : False := by grind
  exact eq1382928

/-- `Equation4470`: `x ◇ (y ◇ y) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4470 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4470 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4470.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X0) X1) := by
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
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
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
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X1) X2) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq30
    | exact resolve eq30 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
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
  clear eq25
  have eq135 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X0) X2
       have i₂ := eq29 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X1 X1 (M.op X0 X0)
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X1)) = (M.op (M.op X2 X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq29 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq29 eq13
    | (have j1 := eq29 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq41
  have eq167 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq151 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq151
    | exact resolve eq151 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq185 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k (M.op X0 X0) X2) ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X0 X0) X2
       have i₂ := eq29 X1 X0 X2
       grind)
    | exact superpose eq29 eq49
    | (have j0 := eq49 (M.op X0 X0) X2
       have j1 := eq29 X1 X1 X2
       grind)
    | (have r₁ := eq49 (M.op X0 X0) X2
       have r₂ := eq29 X0 X0 X2
       grind)
    | exact resolve eq49 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq186 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op X0 X0) X1
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq49
    | (have j0 := eq49 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq49 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact resolve eq49 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq167 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq167 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq167
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq167 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq300 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq308 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq318 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq167
    | (have j1 := eq33 X1 X0
       grind)
    | exact resolve eq167 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq333 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq318
    | (have j0 := eq318 X0 X1
       grind)
    | exact resolve eq318 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq338 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq300
    | (have j0 := eq300 X0
       grind)
    | exact resolve eq300 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq740 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq822 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq740 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq740
    | (have j0 := eq740 X0 X1
       grind)
    | exact resolve eq740 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq1581 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq8
    | (have j1 := eq44 X0 X0
       grind)
    | exact resolve eq8 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1583 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq44 X0 X0
       grind)
    | exact resolve eq12 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq295
       have i₂ := eq822 y x
       grind)
    | exact superpose eq822 eq295
    | (have j1 := eq822 (σ y) (σ x)
       grind)
    | (have r₁ := eq295
       have r₂ := eq822 y x
       grind)
    | exact resolve eq295 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1837 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1836
  have eq1848 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq167
    | exact resolve eq167 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq1851 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq8
    | exact resolve eq8 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1864 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq49 (σ x) (σ x)
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq49
    | (have j0 := eq49 (σ x) (σ x)
       grind)
    | exact resolve eq49 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1867 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1864
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq1864
    | exact resolve eq1864 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq1871 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1848
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1848
    | exact resolve eq1848 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq1955 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq822 y x
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq822
    | (have j0 := eq822 y x
       grind)
    | exact resolve eq822 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq1871
  have eq1956 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq1955
  have eq1987 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq308 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq308
    | exact resolve eq308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2007 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq308 x x
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq308
    | exact resolve eq308 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq2036 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2007
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2007
    | exact resolve eq2007 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2039 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1987 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1987
    | (have j0 := eq1987 X0 X1
       grind)
    | exact resolve eq1987 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987
  have eq2526 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq281
    | (have j0 := eq281 X1 (τ X0)
       grind)
    | exact resolve eq281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2637 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2526 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq2526
    | (have j0 := eq2526 X0 X1
       grind)
    | exact resolve eq2526 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2526
  have eq2647 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2637 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2637
    | (have j0 := eq2637 X0 X1
       grind)
    | exact resolve eq2637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq5608 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (M.op (σ X0) (σ X0)) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq5609 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5608 X0 X1
       have i₂ := eq8 (σ X0) (σ X0)
       grind)
    | exact superpose eq8 eq5608
    | (have j0 := eq5608 X0 X1
       grind)
    | exact resolve eq5608 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5608
  have eq5628 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq91
    | (have j0 := eq91 X1 (σ X0)
       grind)
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq5699 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5628 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5628
    | (have j0 := eq5628 X0 X1
       grind)
    | exact resolve eq5628 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5628
  have eq8917 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq2039 X0 X1
       grind)
    | exact superpose eq2039 eq24
    | (have j1 := eq2039 X0 X1
       grind)
    | exact resolve eq24 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq9717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq295
       have i₂ := eq2647 x y
       grind)
    | exact superpose eq2647 eq295
    | (have j1 := eq2647 x y
       grind)
    | (have r₁ := eq295
       have r₂ := eq2647 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq295
       have r₂ := eq2647 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq295 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq2647
  have eq9787 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ x = y := by grind
  clear eq9717
  have eq10671 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq244 (σ X1) X0
       grind)
    | exact superpose eq244 eq24
    | (have j1 := eq244 (σ X1) X0
       grind)
    | exact resolve eq24 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq244
  have eq10701 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10671 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq10671
    | (have j0 := eq10671 X0 X1
       grind)
    | exact resolve eq10671 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10671
  have eq10740 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10701 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq10701
    | (have j0 := eq10701 X0 X1
       grind)
    | exact resolve eq10701 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10701
  have eq17480 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2036
       grind)
    | exact superpose eq2036 eq9
    | exact resolve eq9 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq17552 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17480
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq17480
    | exact resolve eq17480 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17480
  have eq18205 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30 x x
       have i₂ := eq17552
       grind)
    | exact superpose eq17552 eq30
    | exact resolve eq30 eq17552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17552
  have eq18233 : y = (M.op x x) ∨ x = y := by grind
  clear eq18205
  have eq27786 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10740 x x
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq10740
    | (have j0 := eq10740 x x
       grind)
    | exact resolve eq10740 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27881 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq27786
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq27786
    | exact resolve eq27786 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27786
  have eq33534 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5699 x x
       have i₂ := eq27881
       grind)
    | exact superpose eq27881 eq5699
    | exact resolve eq5699 eq27881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5699 eq27881
  have eq33538 : x = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq33534
  have eq42519 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq338 x
       have i₂ := eq33538
       grind)
    | exact superpose eq33538 eq338
    | (have j0 := eq338 x
       grind)
    | exact resolve eq338 eq33538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq33538
  have eq42560 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq42519
       have r₂ := eq1867
       grind)
    | exact resolve eq42519 eq1867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867 eq42519
  have eq42564 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq330 x
       grind)
    | (have r₁ := eq42560
       have r₂ := eq330 x
       grind)
    | exact resolve eq42560 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq42560
  have eq43404 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1837
       have i₂ := eq42564
       grind)
    | exact superpose eq42564 eq1837
    | exact resolve eq1837 eq42564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43431 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq42564
       grind)
    | exact superpose eq42564 eq8
    | exact resolve eq8 eq42564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42564
  have eq43543 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq43404
  have eq81414 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8917 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8917
    | (have j0 := eq8917 X1 (τ X0)
       grind)
    | exact resolve eq8917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81499 : ∀ X0 : G, (k (τ (σ X0)) X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq8917 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81500 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq81499 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq81499
    | (have j0 := eq81499 X0
       grind)
    | exact resolve eq81499 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81499
  have eq81539 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81414 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq81414
    | (have j0 := eq81414 X0 X1
       grind)
    | exact resolve eq81414 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81414
  have eq81624 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq81500 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq81500
    | (have j0 := eq81500 X0
       have j1 := eq30 X0 X0
       grind)
    | (have r₁ := eq81500 X0
       have r₂ := eq30 X0 X0
       grind)
    | exact resolve eq81500 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81660 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq81624 X0
       have j1 := eq81500 X0
       grind)
    | (have r₁ := eq81624 X0
       have r₂ := eq81500 X0
       grind)
    | exact resolve eq81624 eq81500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81624
  have eq81716 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (τ (M.op (σ X1) (σ X1))) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq81660 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq81660 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq81660
    | (have j0 := eq81660 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq81660 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq81660 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq81660 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81660
  have eq82654 : (τ (σ y)) = (k (τ (σ x)) x) ∨ x = (τ (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq8917 (σ x) x
       have i₂ := eq9787
       grind)
    | exact superpose eq9787 eq8917
    | exact resolve eq8917 eq9787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8917 eq9787
  have eq82698 : (k x x) = (τ (σ y)) ∨ x = (τ (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq82654
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq82654
    | exact resolve eq82654 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82654
  have eq82719 : y = (k x x) ∨ x = (τ (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq82698
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq82698
    | exact resolve eq82698 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82698
  have eq82720 : y = (k x x) ∨ x = (τ (σ y)) ∨ x = y := by grind
  clear eq82719
  have eq82728 : x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq82720
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq82720
    | exact resolve eq82720 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82720
  have eq82729 : y = (k x x) ∨ x = y := by grind
  clear eq82728
  have eq84681 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ (τ X0))) = (M.op X1 (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1581 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1581
    | exact resolve eq1581 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq84689 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X1 (k X0 X0)) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq84681 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84681
    | (have j0 := eq84681 X0 X1
       grind)
    | exact resolve eq84681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84681
  have eq84693 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X1 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84689 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84689
    | (have j0 := eq84689 X0 X1
       grind)
    | exact resolve eq84689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84689
  have eq87942 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (k X1 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1
       have i₂ := eq84693 X1 X0
       grind)
    | exact superpose eq84693 eq8
    | (have j1 := eq84693 X1 X1
       grind)
    | exact resolve eq8 eq84693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84693
  have eq88948 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1851 (σ x)
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq1851
    | exact resolve eq1851 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851
  have eq89013 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq88948
  have eq91005 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x x)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq87942 X0 x
       have i₂ := eq82729
       grind)
    | exact superpose eq82729 eq87942
    | exact resolve eq87942 eq82729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82729 eq87942
  have eq91046 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq91005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91005
  have eq91131 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x x)) = (M.op X0 (M.op (M.op x x) y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op x x)
       have i₂ := eq91046 (M.op x x)
       grind)
    | exact superpose eq91046 eq8
    | exact resolve eq8 eq91046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91046
  have eq91308 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x x)) = (M.op X0 (M.op x (M.op y y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq91131 X0
       have i₂ := eq8 x y
       grind)
    | exact superpose eq8 eq91131
    | exact resolve eq91131 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91131
  have eq92340 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1583 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq92341 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq92340 X0 X1
       have j1 := eq281 X1 X0
       grind)
    | (have r₁ := eq92340 (k X1 X1) X0
       have r₂ := eq281 X0 X1
       grind)
    | (have r₁ := eq92340 X0 (σ (k X1 X1))
       have r₂ := eq281 (σ X0) X1
       grind)
    | (have r₁ := eq92340 X1 X0
       have r₂ := eq281 X0 X1
       grind)
    | exact resolve eq92340 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq92340
  have eq92408 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq92341 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq92341 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq92341 eq16
    | (have j1 := eq92341 (τ X1) X0
       grind)
    | exact resolve eq16 eq92341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92409 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq92341 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq92341 X0 (σ X0)
       grind)
    | exact superpose eq92341 eq9
    | (have j1 := eq92341 X1 X0
       grind)
    | exact resolve eq9 eq92341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92341
  have eq92467 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq92408 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq92408
    | (have j0 := eq92408 X0 X1
       grind)
    | exact resolve eq92408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92408
  have eq92477 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq92467 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92467
    | (have j0 := eq92467 X0 X1
       grind)
    | exact resolve eq92467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92467
  have eq92621 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq92477
  have eq94687 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq92409 (σ X1) X0
       grind)
    | exact superpose eq92409 eq13
    | (have j1 := eq92409 (σ X1) X0
       grind)
    | exact resolve eq13 eq92409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92409
  have eq94711 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94687 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq94687
    | (have j0 := eq94687 X0 X1
       grind)
    | exact resolve eq94687 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94687
  have eq96691 : ∀ X0 : G, y ≠ y ∨ y = (k y X0) ∨ (k X0 x) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq185 x x x
       have i₂ := eq18233
       grind)
    | exact superpose eq18233 eq185
    | (have j0 := eq185 X0 x X0
       grind)
    | exact resolve eq185 eq18233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq18233
  have eq96693 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ y = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq96691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96691
  have eq98488 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) ≠ (M.op X0 (M.op X0 X0)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5609 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5609
    | exact resolve eq5609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5609
  have eq98489 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op X0 (M.op X0 X0)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98488 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq98488
    | (have j0 := eq98488 X0 X1
       grind)
    | exact resolve eq98488 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98488
  have eq98492 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98489 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq98489
    | (have j0 := eq98489 X0 X1
       grind)
    | exact resolve eq98489 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq98489
  have eq100525 : y ≠ y ∨ y = (τ (M.op (σ y) (σ y))) ∨ (M.op y x) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq81500 y
       have i₂ := eq96693 y
       grind)
    | exact superpose eq96693 eq81500
    | (have j0 := eq81500 y
       have j1 := eq96693 y
       grind)
    | (have r₁ := eq81500 y
       have r₂ := eq96693 y
       grind)
    | exact resolve eq81500 eq96693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81500 eq96693
  have eq100556 : y = (τ (M.op (σ y) (σ y))) ∨ (M.op y x) = (k y x) ∨ x = y := by grind
  clear eq100525
  have eq100585 : y = (τ (M.op (σ y) (σ y))) ∨ (M.op y x) = (k y x) := by
    first
    | (have j1 := eq81716 x y
       grind)
    | (have r₁ := eq100556
       have r₂ := eq81716 y (τ (M.op (σ y) (σ y)))
       grind)
    | (have r₁ := eq100556
       have r₂ := eq81716 (τ (M.op (σ y) (σ y))) y
       grind)
    | (have r₁ := eq100556
       have r₂ := eq81716 (M.op y x) (k y x)
       grind)
    | exact resolve eq100556 eq81716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81716 eq100556
  have eq101078 : y = (k y y) ∨ y = (k y y) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq10740 y y
       have i₂ := eq100585
       grind)
    | exact superpose eq100585 eq10740
    | (have j0 := eq10740 y y
       grind)
    | exact resolve eq10740 eq100585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10740 eq100585
  have eq101103 : y = (k y y) ∨ (M.op y x) = (k y x) := by grind
  clear eq101078
  have eq101201 : (τ y) = (τ (M.op y y)) ∨ (τ y) = (τ (M.op y y)) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq81539 y y
       have i₂ := eq101103
       grind)
    | exact superpose eq101103 eq81539
    | (have j0 := eq81539 y y
       grind)
    | exact resolve eq81539 eq101103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81539 eq101103
  have eq101202 : (τ y) = (τ (M.op y y)) ∨ (M.op y x) = (k y x) := by grind
  clear eq101201
  have eq101255 : ∀ X0 : G, (k (τ y) (τ X0)) = (τ (k (M.op y y) X0)) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq52 X0 (M.op y y)
       have i₂ := eq101202
       grind)
    | exact superpose eq101202 eq52
    | exact resolve eq52 eq101202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101202
  have eq101266 : ∀ X0 : G, (τ (k y X0)) = (τ (k (M.op y y) X0)) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq101255 X0
       have i₂ := eq52 X0 y
       grind)
    | exact superpose eq52 eq101255
    | exact resolve eq101255 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq101255
  have eq110978 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43431 (σ x)
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq43431
    | exact resolve eq43431 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837 eq43431
  have eq111034 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq110978
  have eq111049 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89013
       have i₂ := eq111034
       grind)
    | exact superpose eq111034 eq89013
    | exact resolve eq89013 eq111034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89013 eq111034
  have eq111077 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq111049
  have eq111286 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq111077
       grind)
    | exact superpose eq111077 eq14
    | exact resolve eq14 eq111077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111077
  have eq111344 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq111286
       have i₂ := eq1956
       grind)
    | exact superpose eq1956 eq111286
    | exact resolve eq111286 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956 eq111286
  have eq111347 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq111344
  have eq111349 : y = (M.op x x) := by
    first
    | (have r₁ := eq111347
       have r₂ := eq43543
       grind)
    | exact resolve eq111347 eq43543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43543 eq111347
  have eq111369 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 x X0
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq8
    | exact resolve eq8 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111424 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k (M.op X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq186 X0 x
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq186
    | (have j0 := eq186 X0 x
       grind)
    | exact resolve eq186 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq111612 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 X0)) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq135 x x x
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq135
    | exact resolve eq135 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq111820 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq111369 x
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq111369
    | exact resolve eq111369 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111369
  have eq126485 : (M.op y y) = (k (M.op y y) x) := by
    first
    | (have j0 := eq111424 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111424
  have eq127824 : (M.op y y) = (M.op y x) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq111612 x
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq111612
    | exact resolve eq111612 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111612
  have eq127889 : (M.op x y) = (M.op y y) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq127824
       have i₂ := eq111820
       grind)
    | exact superpose eq111820 eq127824
    | exact resolve eq127824 eq111820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127824
  have eq127905 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq127889
       have i₂ := eq111820
       grind)
    | exact superpose eq111820 eq127889
    | exact resolve eq127889 eq111820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127889
  have eq187230 : ∀ X0 : G, (k (M.op y y) X0) = (σ (τ (k y X0))) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op y y) X0)
       have i₂ := eq101266 X0
       grind)
    | exact superpose eq101266 eq10
    | exact resolve eq10 eq101266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101266
  have eq187234 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq187230 X0
       have i₂ := eq10 (k y X0)
       grind)
    | exact superpose eq10 eq187230
    | exact resolve eq187230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187230
  have eq187238 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq187234 X0
       have i₂ := eq111820
       grind)
    | exact superpose eq111820 eq187234
    | (have j0 := eq187234 X0
       grind)
    | exact resolve eq187234 eq111820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111820 eq187234
  have eq187262 : (M.op y y) = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq126485
       have i₂ := eq187238 x
       grind)
    | exact superpose eq187238 eq126485
    | exact resolve eq126485 eq187238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126485 eq187238
  have eq187408 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (k y x) := by grind
  clear eq187262
  have eq187411 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq187408
       have r₂ := eq127905
       grind)
    | exact resolve eq187408 eq127905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127905 eq187408
  have eq200033 : ∀ X0 X1 : G, (k X1 X0) ≠ (M.op X1 (M.op X1 X1)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq98492 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98492
    | exact resolve eq98492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98492
  have eq200057 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq200033 X1 X0
       have i₂ := eq92621 X0
       grind)
    | exact superpose eq92621 eq200033
    | (have j0 := eq200033 X1 X0
       have j1 := eq92621 X0
       grind)
    | exact resolve eq200033 eq92621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92621 eq200033
  have eq200084 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq200057 X0 X1
       have j1 := eq30 X1 X0
       grind)
    | (have r₁ := eq200057 X1 X0
       have r₂ := eq30 X0 X1
       grind)
    | exact resolve eq200057 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq200057
  have eq200175 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq200084 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200084
  have eq200176 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq200175 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200175
  have eq200993 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq200176 (σ X0)
       grind)
    | exact superpose eq200176 eq13
    | exact resolve eq13 eq200176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201242 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq200993 X0
       have i₂ := eq200176 X0
       grind)
    | exact superpose eq200176 eq200993
    | exact resolve eq200993 eq200176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200993
  have eq202361 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq201242 X0
       grind)
    | exact superpose eq201242 eq8
    | exact resolve eq8 eq201242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205402 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq202361 x X0
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq202361
    | exact resolve eq202361 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202361
  have eq205662 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (M.op (σ x) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq205402 (σ X0)
       have i₂ := eq201242 X0
       grind)
    | exact superpose eq201242 eq205402
    | exact resolve eq205402 eq201242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205402
  have eq206719 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq205662 x
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq205662
    | exact resolve eq205662 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205662
  have eq206903 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq333 x y
       have i₂ := eq206719
       grind)
    | exact superpose eq206719 eq333
    | (have j0 := eq333 x y
       grind)
    | exact resolve eq333 eq206719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq206914 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq94711 y x
       have i₂ := eq206719
       grind)
    | exact superpose eq206719 eq94711
    | (have j0 := eq94711 y x
       grind)
    | exact resolve eq94711 eq206719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94711 eq206719
  have eq206961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq206914
       have i₂ := eq187411
       grind)
    | exact superpose eq187411 eq206914
    | exact resolve eq206914 eq187411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206914
  have eq206972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq206903
       have i₂ := eq187411
       grind)
    | exact superpose eq187411 eq206903
    | exact resolve eq206903 eq187411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206903
  have eq207005 : x = (k y y) := by
    first
    | (have r₁ := eq206961
       have r₂ := eq14
       grind)
    | exact resolve eq206961 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206961
  have eq207016 : y = (k y x) := by
    first
    | (have r₁ := eq206972
       have r₂ := eq14
       grind)
    | exact resolve eq206972 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206972
  have eq207040 : x = (M.op y y) := by
    first
    | (have i₁ := eq207005
       have i₂ := eq200176 y
       grind)
    | exact superpose eq200176 eq207005
    | exact resolve eq207005 eq200176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200176 eq207005
  have eq207195 : y = (M.op x y) := by
    first
    | (have i₁ := eq187411
       have i₂ := eq207016
       grind)
    | exact superpose eq207016 eq187411
    | exact resolve eq187411 eq207016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187411 eq207016
  have eq208081 : (M.op x (M.op x x)) = (M.op y (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq91308 y
       have i₂ := eq207040
       grind)
    | exact superpose eq207040 eq91308
    | exact resolve eq91308 eq207040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91308
  have eq208412 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq208081
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq208081
    | exact resolve eq208081 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111349 eq208081
  have eq208579 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq208412
       have i₂ := eq207040
       grind)
    | exact superpose eq207040 eq208412
    | exact resolve eq208412 eq207040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207040 eq208412
  have eq208651 : x = y ∨ x = y := by
    first
    | (have i₁ := eq208579
       have i₂ := eq207195
       grind)
    | exact superpose eq207195 eq208579
    | exact resolve eq208579 eq207195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207195 eq208579
  have eq208652 : x = y := by grind
  clear eq208651
  have eq208683 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq208652
       grind)
    | exact superpose eq208652 eq14
    | exact resolve eq14 eq208652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208652
  have eq209573 : False := by grind
  exact eq209573

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation4478 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4478 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq492 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq496 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq492 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq492 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq492 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq492 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq531 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq496 (σ X1) (σ X0)
       grind)
    | exact superpose eq496 eq13
    | exact resolve eq13 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq531 X0 X1
       have i₂ := eq496 X1 X0
       grind)
    | exact superpose eq496 eq531
    | exact resolve eq531 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq531
  have eq1747 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq542 x y
       grind)
    | exact superpose eq542 eq14
    | (have r₁ := eq14
       have r₂ := eq542 x y
       grind)
    | exact resolve eq14 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq1778 : False := by grind
  exact eq1778

/-- `Equation4485`: `x ◇ (y ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4485 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4485 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X0 X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X1 X2) X1 X2
       have i₂ := eq8 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 X0)
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq8 X0 (M.op X1 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X1) = (M.op X1 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq60 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X2 X3 X4 (M.op X0 X0)
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq19 (M.op X1 X2) X1 X2 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X2 X4) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X0 X3) X2 X4
       have i₂ := eq19 X0 X3 (M.op X2 X2) X1
       grind)
    | (have i₁ := eq8 (M.op X0 X3) X2 X4
       have i₂ := eq19 X0 X1 (M.op X2 X2) X3
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq101 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq40 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq40 eq13
    | (have j1 := eq40 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X2 (τ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq40 (τ X1) X2 X0
       grind)
    | exact superpose eq40 eq16
    | (have j1 := eq40 (τ X1) X2 X2
       grind)
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq40 X1 (σ X0) X2
       grind)
    | exact superpose eq40 eq47
    | (have j1 := eq40 X1 X1 X2
       grind)
    | exact resolve eq47 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq121 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112
    | (have j0 := eq112 X0 X1 X2
       grind)
    | exact resolve eq112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq127 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op (M.op X4 X5) (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X4 X5 (M.op X0 X2) X3
       have i₂ := eq19 X0 X2 (M.op X0 X2) X1
       grind)
    | (have i₁ := eq21 X4 X5 (M.op X0 X2) X3
       have i₂ := eq19 X0 X1 (M.op X0 X2) X2
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 (M.op X2 X3) X1 X0 X4
       have i₂ := eq21 X2 X3 X1 X0
       grind)
    | (have i₁ := eq19 X0 X1 (M.op X2 X2) X3
       have i₂ := eq21 X0 X1 X2 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq19
    | exact resolve eq19 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 (M.op X1 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq105 X0 (M.op X1 X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq105
    | (have j0 := eq105 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq105 (M.op X0 (M.op X0 X0)) X0
       have r₂ := eq8 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq105 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 X1) ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq33 X1 X0 x X3
       grind)
    | exact superpose eq33 eq8
    | (have j1 := eq33 X1 X1 x X3
       grind)
    | exact resolve eq8 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq845 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X4 X5) X0) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq60 x x X4 X5 X0
       have i₂ := eq168 X0 X1 x x X4
       grind)
    | (have i₁ := eq60 X0 X1 x x (M.op X1 X1)
       have i₂ := eq168 (M.op (M.op X0 X1) x) X1 x x X4
       grind)
    | exact superpose eq168 eq60
    | exact resolve eq60 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq168
  have eq1162 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 X3 X4
       have i₂ := eq845 X2 X3 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X4 x) X1 X2
       have i₂ := eq845 (M.op X1 X1) X1 X4 x
       grind)
    | exact superpose eq845 eq8
    | exact resolve eq8 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2119 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 (σ X0)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X1 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq121
    | (have j0 := eq121 X0 (σ X0) X2
       grind)
    | exact resolve eq121 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2174 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq38 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq11 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2242 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq2246 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2174 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq2174 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq2174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2263 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2246 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq2246
    | (have j0 := eq2246 (τ X0) X1
       grind)
    | exact resolve eq2246 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2267 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2263 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2263
    | (have j0 := eq2263 X0 X1
       grind)
    | exact resolve eq2263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq2271 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2267 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2267
    | (have j0 := eq2267 X0 X1
       grind)
    | exact resolve eq2267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq2480 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2271 (τ X0) X1
       have i₂ := eq82 X0 X0
       grind)
    | exact superpose eq82 eq2271
    | (have j0 := eq2271 (τ X0) X1
       grind)
    | exact resolve eq2271 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq2271
  have eq3192 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq3341 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3192 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3192
    | (have j0 := eq3192 X0 X1
       grind)
    | exact resolve eq3192 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq4216 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X0
       have i₂ := eq3341 X1 X0
       grind)
    | exact superpose eq3341 eq105
    | (have j0 := eq105 X0 X0
       have j1 := eq3341 X1 X0
       grind)
    | (have r₁ := eq105 X1 X1
       have r₂ := eq3341 X0 X1
       grind)
    | exact resolve eq105 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq4261 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4216
  have eq7234 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2246 X0 X1
       have i₂ := eq4261 X0 X2
       grind)
    | exact superpose eq4261 eq2246
    | (have j0 := eq2246 X0 X1
       have j1 := eq4261 X0 X2
       grind)
    | exact resolve eq2246 eq4261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246 eq4261
  have eq7284 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq7234 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7234
  have eq8595 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2242 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq2242
    | (have j0 := eq2242 (τ X0)
       grind)
    | exact resolve eq2242 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8611 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8595 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8595
    | (have j0 := eq8595 X0
       grind)
    | exact resolve eq8595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8595
  have eq8618 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8611 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8611
    | (have j0 := eq8611 X0
       grind)
    | exact resolve eq8611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8611
  have eq9341 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq101 x y X0
       grind)
    | exact superpose eq101 eq14
    | (have j1 := eq101 X0 y X0
       grind)
    | exact resolve eq14 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq9462 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq9341 X0
       have j1 := eq7284 y X0 x
       grind)
    | (have r₁ := eq9341 X0
       have r₂ := eq7284 y x x
       grind)
    | exact resolve eq9341 eq7284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7284 eq9341
  have eq9497 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8618 (σ y)
       have i₂ := eq9462 (σ y)
       grind)
    | exact superpose eq9462 eq8618
    | (have j0 := eq8618 (σ y)
       grind)
    | (have r₁ := eq8618 (σ y)
       have r₂ := eq9462 (σ y)
       grind)
    | exact resolve eq8618 eq9462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9499 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2480 (σ y) X0
       have i₂ := eq9462 (σ y)
       grind)
    | exact superpose eq9462 eq2480
    | (have j0 := eq2480 (σ y) X0
       grind)
    | exact resolve eq2480 eq9462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9462
  have eq9525 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq9499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9499
  have eq9527 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq9497
  have eq9535 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9525 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq9525
    | exact resolve eq9525 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9525
  have eq9700 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8618 y
       have i₂ := eq9535 y
       grind)
    | exact superpose eq9535 eq8618
    | (have j0 := eq8618 y
       grind)
    | (have r₁ := eq8618 y
       have r₂ := eq9535 y
       grind)
    | exact resolve eq8618 eq9535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9707 : ∀ X0 X1 : G, (M.op X0 y) = X0 ∨ (M.op y X1) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq36 y X1 X0
       have i₂ := eq9535 X0
       grind)
    | exact superpose eq9535 eq36
    | (have j0 := eq36 y X1 x
       grind)
    | exact resolve eq36 eq9535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq9535
  have eq9727 : y = (M.op y y) := by grind
  clear eq9700
  have eq10045 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq845 X0 y X1 X2
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq845
    | exact resolve eq845 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10050 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq8
    | exact resolve eq8 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10071 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op y (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X1 y x y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq80
    | exact resolve eq80 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq10087 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 X1 y y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq845
    | exact resolve eq845 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq10089 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1162 X0 X1 X2 y y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq1162
    | exact resolve eq1162 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10100 : ∀ X0 X2 : G, (M.op y y) = (M.op y (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq10071 X0 x X2
       have i₂ := eq10089 X0 x y
       grind)
    | exact superpose eq10089 eq10071
    | exact resolve eq10071 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10071
  have eq10119 : ∀ X0 X2 : G, y = (M.op y (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq10100 X0 X2
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq10100
    | exact resolve eq10100 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9727 eq10100
  have eq19794 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1162 X0 X1 X2 (σ y) (σ y)
       have i₂ := eq9527
       grind)
    | exact superpose eq9527 eq1162
    | exact resolve eq1162 eq9527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq19796 : y = (M.op y (σ y)) := by
    first
    | (have i₁ := eq10119 (σ y) (σ y)
       have i₂ := eq9527
       grind)
    | exact superpose eq9527 eq10119
    | exact resolve eq10119 eq9527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19801 : ∀ X2 : G, (M.op (σ y) X2) = (M.op y X2) := by
    intro X2
    first
    | (have i₁ := eq19794 x x X2
       have i₂ := eq10089 x x X2
       grind)
    | exact superpose eq10089 eq19794
    | exact resolve eq19794 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19794
  have eq22032 : (σ y) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq9527
       have i₂ := eq19801 (σ y)
       grind)
    | exact superpose eq19801 eq9527
    | exact resolve eq9527 eq19801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9527 eq19801
  have eq22202 : y = (σ y) := by
    first
    | (have i₁ := eq22032
       have i₂ := eq19796
       grind)
    | exact superpose eq19796 eq22032
    | exact resolve eq22032 eq19796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19796 eq22032
  have eq23116 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq14
    | exact resolve eq14 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23123 : ∀ X0 : G, (k y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq13
    | exact resolve eq13 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23137 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq47 y X0
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq47
    | exact resolve eq47 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq23152 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq23116
       have i₂ := eq10050 (σ x)
       grind)
    | exact superpose eq10050 eq23116
    | exact resolve eq23116 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23116
  have eq30888 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k (σ (M.op (M.op X4 X5) (M.op X1 X3))) X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq103 (M.op (M.op X4 X5) (M.op X1 X3)) X0 X6
       have i₂ := eq127 X1 X2 X3 (τ X0) X4 X5
       grind)
    | exact superpose eq127 eq103
    | (have j0 := eq103 X0 X0 X6
       grind)
    | exact resolve eq103 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq127
  have eq30891 : ∀ X0 X1 X2 X3 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k (σ (M.op y (M.op X1 X3))) X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq30888 X0 X1 X2 X3 x x X6
       have i₂ := eq10089 x x (M.op X1 X3)
       grind)
    | exact superpose eq10089 eq30888
    | (have j0 := eq30888 X0 X1 X2 X3 x x X6
       grind)
    | exact resolve eq30888 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30888
  have eq31059 : ∀ X0 X1 X2 X3 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k (σ y) X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq30891 X0 X1 X2 X3 X6
       have i₂ := eq10119 X1 X3
       grind)
    | exact superpose eq10119 eq30891
    | (have j0 := eq30891 X0 X1 X2 X3 X6
       grind)
    | exact resolve eq30891 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30891
  have eq31218 : ∀ X0 X1 X2 X3 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq31059 X0 X1 X2 X3 X6
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq31059
    | (have j0 := eq31059 X0 X1 X2 X3 X6
       grind)
    | exact resolve eq31059 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31059
  have eq31332 : ∀ X0 X1 X3 X6 : G, (σ (M.op (τ X0) (M.op y (M.op X1 X3)))) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X3 X6
    first
    | (have i₁ := eq31218 X0 X1 x X3 X6
       have i₂ := eq10089 X1 x (M.op X1 X3)
       grind)
    | exact superpose eq10089 eq31218
    | (have j0 := eq31218 X0 X1 x X3 X6
       grind)
    | exact resolve eq31218 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31218
  have eq31341 : ∀ X0 X6 : G, (σ (M.op (τ X0) y)) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X6
    first
    | (have i₁ := eq31332 X0 x x X6
       have i₂ := eq10119 x x
       grind)
    | exact superpose eq10119 eq31332
    | (have j0 := eq31332 X0 x x X6
       grind)
    | exact resolve eq31332 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31332
  have eq31349 : ∀ X0 X6 : G, (σ (M.op y (τ X0))) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X6
    first
    | (have i₁ := eq31341 X0 X6
       have i₂ := eq10050 (τ X0)
       grind)
    | exact superpose eq10050 eq31341
    | (have j0 := eq31341 X0 X6
       grind)
    | exact resolve eq31341 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31341
  have eq38564 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op y X0) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq485 X0 X1 X2
       have i₂ := eq10087 X0 X1
       grind)
    | exact superpose eq10087 eq485
    | (have j0 := eq485 X0 X1 X2
       grind)
    | exact resolve eq485 eq10087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41672 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2119 X0 X1 y
       have i₂ := eq23123 X0
       grind)
    | exact superpose eq23123 eq2119
    | (have j0 := eq2119 X0 X1 x
       grind)
    | exact resolve eq2119 eq23123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119
  have eq99839 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq9707 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9707
  have eq103998 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq99839 (M.op X0 X0)
       have i₂ := eq485 y X0 X1
       grind)
    | exact superpose eq485 eq99839
    | (have j0 := eq99839 (M.op X0 X0)
       have j1 := eq485 X0 X0 X1
       grind)
    | (have r₁ := eq99839 (M.op y y)
       have r₂ := eq485 y y x
       grind)
    | exact resolve eq99839 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq99839
  have eq104059 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) y) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq103998 X0 X1
       have j1 := eq38564 X0 X0 X1
       grind)
    | (have r₁ := eq103998 X1 X1
       have r₂ := eq38564 X1 X1 x
       grind)
    | (have r₁ := eq103998 y X1
       have r₂ := eq38564 y y x
       grind)
    | exact resolve eq103998 eq38564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38564 eq103998
  have eq104106 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104059 X0 X1
       have i₂ := eq8 y X0 X0
       grind)
    | exact superpose eq8 eq104059
    | (have j0 := eq104059 X0 X1
       grind)
    | exact resolve eq104059 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104059
  have eq104153 : ∀ X0 X1 : G, y = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104106 X0 X1
       have i₂ := eq10119 X0 X0
       grind)
    | exact superpose eq10119 eq104106
    | (have j0 := eq104106 X0 X1
       grind)
    | exact resolve eq104106 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10119 eq104106
  have eq121300 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23137 X0
       have i₂ := eq104153 X0 y
       grind)
    | exact superpose eq104153 eq23137
    | (have j1 := eq104153 X0 x
       grind)
    | exact resolve eq23137 eq104153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23137 eq104153
  have eq535751 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k y X1) = (σ (M.op y (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (τ X1)
       have i₂ := eq31349 X1 (τ X0)
       grind)
    | exact superpose eq31349 eq15
    | (have j1 := eq31349 X1 x
       grind)
    | exact resolve eq15 eq31349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq31349
  have eq535752 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k y X1) = (σ (M.op y (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq535751 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq535751
    | (have j0 := eq535751 X0 X1
       grind)
    | exact resolve eq535751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535751
  have eq535761 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k y X1) = (σ (M.op y (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq535752 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq535752
    | (have j0 := eq535752 X0 X1
       grind)
    | exact resolve eq535752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535752
  have eq541829 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op y (τ X0))) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq8618 X0
       have i₂ := eq535761 X0 X0
       grind)
    | exact superpose eq535761 eq8618
    | (have j0 := eq8618 X0
       have j1 := eq535761 X0 X0
       grind)
    | (have r₁ := eq8618 x
       have r₂ := eq535761 x x
       grind)
    | exact resolve eq8618 eq535761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535761
  have eq541871 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op y (τ X0))) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq541829 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541829
  have eq561204 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3341 y X0
       have i₂ := eq41672 X0 X1
       grind)
    | exact superpose eq41672 eq3341
    | (have j0 := eq3341 X0 X0
       have j1 := eq41672 X0 X1
       grind)
    | exact resolve eq3341 eq41672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341 eq41672
  have eq561262 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq561204 X0 X1
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq561204 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq561204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561204
  have eq563551 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq182 X0 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq563552 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq563551 x
       have i₂ := eq10087 x x
       grind)
    | exact superpose eq10087 eq563551
    | exact resolve eq563551 eq10087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10087 eq563551
  have eq563832 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (σ (M.op y (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y (τ X0))
       have i₂ := eq563552 (τ X0)
       grind)
    | exact superpose eq563552 eq16
    | exact resolve eq16 eq563552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563552
  have eq564652 : ∀ X0 : G, (k y X0) = (k (k y X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq563832 X0
       have i₂ := eq541871 X0
       grind)
    | exact superpose eq541871 eq563832
    | (have j1 := eq541871 X0
       grind)
    | exact resolve eq563832 eq541871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541871 eq563832
  have eq564801 : ∀ X0 : G, (k y X0) = (k (k y X0) X0) := by
    intro X0
    first
    | (have j0 := eq564652 X0
       have j1 := eq11 (k y X0) X0
       grind)
    | (have r₁ := eq564652 x
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq564652 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564652
  have eq564990 : ∀ X0 : G, (k y X0) = (M.op (k y X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (k y X0) X0
       have i₂ := eq564801 X0
       grind)
    | exact superpose eq564801 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq564801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564801
  have eq565271 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (k y X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10045 X1 (k y X0) X0
       have i₂ := eq564990 X0
       grind)
    | exact superpose eq564990 eq10045
    | (have j1 := eq564990 X0
       grind)
    | exact resolve eq10045 eq564990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10045
  have eq567484 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq564990 X0
       have i₂ := eq565271 X0 X0
       grind)
    | exact superpose eq565271 eq564990
    | (have j0 := eq564990 X0
       have j1 := eq565271 X0 x
       grind)
    | exact resolve eq564990 eq565271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564990 eq565271
  have eq567578 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq567484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567484
  have eq573957 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 y)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq121300 X0
       have i₂ := eq10050 X0
       grind)
    | (have i₁ := eq121300 y
       have i₂ := eq10050 y
       grind)
    | exact superpose eq10050 eq121300
    | (have j0 := eq121300 X0
       grind)
    | exact resolve eq121300 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121300
  have eq578633 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq561262 X0 X1
       have i₂ := eq10050 X0
       grind)
    | (have i₁ := eq561262 y X1
       have i₂ := eq10050 y
       grind)
    | exact superpose eq10050 eq561262
    | (have j0 := eq561262 X0 X1
       grind)
    | exact resolve eq561262 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561262
  have eq646029 : ∀ X0 : G, (M.op X0 y) = (σ (k y (τ X0))) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 y)
       have i₂ := eq573957 X0
       grind)
    | exact superpose eq573957 eq10
    | (have j1 := eq573957 X0
       grind)
    | exact resolve eq10 eq573957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573957
  have eq646069 : ∀ X0 : G, (M.op X0 y) = (k (σ y) X0) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq646029 X0
       have i₂ := eq16 X0 y
       grind)
    | exact superpose eq16 eq646029
    | (have j0 := eq646029 X0
       grind)
    | exact resolve eq646029 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq646029
  have eq646084 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq646069 X0
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq646069
    | (have j0 := eq646069 X0
       grind)
    | exact resolve eq646069 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646069
  have eq646275 : ∀ X0 : G, y = X0 ∨ (M.op X0 y) = (k y X0) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq567578 X0
       have i₂ := eq646084 X0
       grind)
    | exact superpose eq646084 eq567578
    | (have j0 := eq567578 X0
       have j1 := eq646084 X0
       grind)
    | exact resolve eq567578 eq646084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567578 eq646084
  have eq646325 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq646275 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646275
  have eq647844 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) y) ∨ (σ X0) = y := by
    intro X0
    first
    | (have i₁ := eq23123 X0
       have i₂ := eq646325 (σ X0)
       grind)
    | exact superpose eq646325 eq23123
    | (have j1 := eq646325 (σ X0)
       grind)
    | exact resolve eq23123 eq646325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23123 eq646325
  have eq648143 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ X0) = y := by
    intro X0
    first
    | (have i₁ := eq647844 X0
       have i₂ := eq10050 (σ X0)
       grind)
    | exact superpose eq10050 eq647844
    | (have j0 := eq647844 X0
       grind)
    | exact resolve eq647844 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10050 eq647844
  have eq701601 : ∀ X0 : G, (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq23152
       have i₂ := eq578633 x X0
       grind)
    | exact superpose eq578633 eq23152
    | (have j1 := eq578633 x X0
       grind)
    | (have r₁ := eq23152
       have r₂ := eq578633 x x
       grind)
    | exact resolve eq23152 eq578633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23152 eq578633
  have eq701615 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq701601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701601
  have eq707298 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2242 x
       have i₂ := eq701615 x
       grind)
    | exact superpose eq701615 eq2242
    | (have j0 := eq2242 x
       grind)
    | exact resolve eq2242 eq701615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq707302 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (k X0 (τ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2480 x X0
       have i₂ := eq701615 x
       grind)
    | exact superpose eq701615 eq2480
    | (have j0 := eq2480 x X0
       grind)
    | exact resolve eq2480 eq701615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq707303 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8618 x
       have i₂ := eq701615 x
       grind)
    | exact superpose eq701615 eq8618
    | (have j0 := eq8618 x
       grind)
    | (have r₁ := eq8618 x
       have r₂ := eq701615 x
       grind)
    | exact resolve eq8618 eq701615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8618 eq701615
  have eq707608 : x = (M.op x x) := by grind
  clear eq707303
  have eq707609 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq707302 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707302
  have eq707613 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq707298
  have eq708628 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10089 x x X0
       have i₂ := eq707608
       grind)
    | exact superpose eq707608 eq10089
    | exact resolve eq10089 eq707608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10089
  have eq709623 : (σ y) = (M.op y (σ (τ x))) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq648143 (τ x)
       have i₂ := eq707609 y
       grind)
    | exact superpose eq707609 eq648143
    | (have j0 := eq648143 (τ x)
       grind)
    | exact resolve eq648143 eq707609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648143 eq707609
  have eq709636 : (σ y) = (M.op x (σ (τ x))) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709623
       have i₂ := eq708628 (σ (τ x))
       grind)
    | exact superpose eq708628 eq709623
    | exact resolve eq709623 eq708628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708628 eq709623
  have eq709812 : (σ y) = (M.op x x) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709636
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq709636
    | exact resolve eq709636 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709636
  have eq709877 : x = (σ y) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709812
       have i₂ := eq707608
       grind)
    | exact superpose eq707608 eq709812
    | exact resolve eq709812 eq707608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709812
  have eq709901 : x = y ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709877
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq709877
    | exact resolve eq709877 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22202 eq709877
  have eq709909 : x = y ∨ x = y := by
    first
    | (have i₁ := eq709901
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq709901
    | exact resolve eq709901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709901
  have eq709910 : x = y := by grind
  clear eq709909
  have eq709913 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq709910
       grind)
    | exact superpose eq709910 eq14
    | exact resolve eq14 eq709910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709910
  have eq710329 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq709913
       have i₂ := eq707608
       grind)
    | exact superpose eq707608 eq709913
    | exact resolve eq709913 eq707608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707608 eq709913
  have eq710336 : False := by grind
  exact eq710336

/-- `Equation4497`: `x ◇ (y ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyy_pxy_Equation4497 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4497 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4497.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq24 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 (M.op x x) X1 x
       have i₂ := eq8 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | (have i₁ := eq8 (M.op X1 X1) X1 X2
       have i₂ := eq8 (M.op X2 X2) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    grind
  have eq100 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X2 X3 (M.op X1 X1)
       have i₂ := eq8 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq24 X2 X3 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq24
    | exact resolve eq24 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X2 X3 (M.op X1 X1)
       have i₂ := eq8 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq28 X2 X3 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq28
    | exact resolve eq28 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq65 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq65
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq65 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq562 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1691 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq562 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1946 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1691 (σ X0)
       grind)
    | exact superpose eq1691 eq13
    | exact resolve eq13 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1948 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0 X0
       have i₂ := eq1691 (τ X0)
       grind)
    | exact superpose eq1691 eq49
    | exact resolve eq49 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1955 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1948 X0
       have i₂ := eq1691 X0
       grind)
    | exact superpose eq1691 eq1948
    | exact resolve eq1948 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq1957 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1946 X0
       have i₂ := eq1691 X0
       grind)
    | exact superpose eq1691 eq1946
    | exact resolve eq1946 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691 eq1946
  have eq2218 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (τ X0) X2
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq8
    | exact resolve eq8 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2226 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (τ X0)
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq24
    | exact resolve eq24 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2231 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X2 (τ X0)
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq28
    | exact resolve eq28 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2337 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (σ X0)
       have i₂ := eq1957 X0
       grind)
    | exact superpose eq1957 eq24
    | exact resolve eq24 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2342 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X2 (σ X0)
       have i₂ := eq1957 X0
       grind)
    | exact superpose eq1957 eq28
    | exact resolve eq28 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2414 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq14
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq14 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq2574 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2414
       have i₂ := eq1957 x
       grind)
    | exact superpose eq1957 eq2414
    | exact resolve eq2414 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957 eq2414
  have eq2728 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op X2 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2218 (τ X0) X2 X1
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq2218
    | exact resolve eq2218 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218
  have eq3631 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (τ (τ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2226 (τ X0) X1 X2
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq2226
    | exact resolve eq2226 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226
  have eq4190 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2231 (τ X0) X1 X2
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq2231
    | exact resolve eq2231 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955 eq2231
  have eq23592 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2574
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq2574
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq2574 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq23598 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq23592
  have eq23605 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq23598
       grind)
    | exact superpose eq23598 eq9
    | exact resolve eq9 eq23598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23598
  have eq23641 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23605
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq23605
    | exact resolve eq23605 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23605
  have eq23642 : y = (M.op x x) := by grind
  clear eq23641
  have eq24113 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x X1
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq8
    | exact resolve eq8 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24151 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X2 X2) y) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X2 x X0 X1
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq100
    | exact resolve eq100 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq24155 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X1) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq156 X1 x X0 X2
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq156
    | exact resolve eq156 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq24157 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 y) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1 x
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq191
    | (have j0 := eq191 X0 X1 x
       grind)
    | exact resolve eq191 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq24192 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2337 x X0 X1
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq2337
    | exact resolve eq2337 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337
  have eq24193 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2342 x X0 X1
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq2342
    | exact resolve eq2342 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq24201 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (τ (τ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2728 x X0 X1
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq2728
    | exact resolve eq2728 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24248 : ∀ X0 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op y (τ (τ y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq24155 X0 x X2
       have i₂ := eq24201 x y
       grind)
    | exact superpose eq24201 eq24155
    | exact resolve eq24155 eq24201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24155
  have eq24251 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (τ (τ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24151 X0 X1 x
       have i₂ := eq24201 x y
       grind)
    | exact superpose eq24201 eq24151
    | exact resolve eq24151 eq24201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24151
  have eq24298 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op y (τ (τ y)))) := by
    intro X0
    first
    | (have i₁ := eq24248 X0 x
       have i₂ := eq24193 X0 x
       grind)
    | exact superpose eq24193 eq24248
    | exact resolve eq24248 eq24193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24193 eq24248
  have eq24301 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (M.op y (τ (τ y))) X1) := by
    intro X1
    first
    | (have i₁ := eq24251 x X1
       have i₂ := eq24192 x X1
       grind)
    | exact superpose eq24192 eq24251
    | exact resolve eq24251 eq24192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24192 eq24251
  have eq75223 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq24113 X0 x
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq24113
    | exact resolve eq24113 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23642
  have eq75324 : ∀ X0 X2 : G, (M.op X0 (τ (τ (M.op X2 X2)))) = (M.op X0 y) := by
    intro X0 X2
    first
    | (have i₁ := eq2728 X2 x X0
       have i₂ := eq24113 X0 x
       grind)
    | exact superpose eq24113 eq2728
    | exact resolve eq2728 eq24113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728
  have eq75325 : ∀ X0 X2 : G, (M.op (τ (τ (M.op X2 X2))) X0) = (M.op X0 y) := by
    intro X0 X2
    first
    | (have i₁ := eq3631 X2 x X0
       have i₂ := eq24113 X0 x
       grind)
    | exact superpose eq24113 eq3631
    | exact resolve eq3631 eq24113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75498 : ∀ X0 X1 X2 : G, (M.op (τ (τ (M.op X2 X2))) X1) = (M.op (M.op (M.op X0 X0) y) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3631 X2 (M.op X0 X0) X1
       have i₂ := eq24113 (M.op X0 X0) X0
       grind)
    | exact superpose eq24113 eq3631
    | exact resolve eq3631 eq24113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq75502 : ∀ X0 X1 X2 : G, (M.op X1 (τ (τ (M.op X2 X2)))) = (M.op X1 (M.op (M.op X0 X0) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4190 X2 X1 (M.op X0 X0)
       have i₂ := eq24113 (M.op X0 X0) X0
       grind)
    | exact superpose eq24113 eq4190
    | exact resolve eq4190 eq24113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4190 eq24113
  have eq75611 : ∀ X1 X2 : G, (M.op X1 (τ (τ (M.op X2 X2)))) = (M.op X1 (M.op y (τ (τ y)))) := by
    intro X1 X2
    first
    | (have i₁ := eq75502 x X1 X2
       have i₂ := eq24201 x y
       grind)
    | exact superpose eq24201 eq75502
    | exact resolve eq75502 eq24201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75502
  have eq75615 : ∀ X1 X2 : G, (M.op (τ (τ (M.op X2 X2))) X1) = (M.op (M.op y (τ (τ y))) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq75498 x X1 X2
       have i₂ := eq24201 x y
       grind)
    | exact superpose eq24201 eq75498
    | exact resolve eq75498 eq24201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24201 eq75498
  have eq76012 : ∀ X1 X2 : G, (M.op X1 (τ (τ (M.op X2 X2)))) = (M.op X1 (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq75611 X1 X2
       have i₂ := eq24298 X1
       grind)
    | exact superpose eq24298 eq75611
    | exact resolve eq75611 eq24298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24298 eq75611
  have eq76016 : ∀ X1 X2 : G, (M.op (τ (τ (M.op X2 X2))) X1) = (M.op (σ y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq75615 X1 X2
       have i₂ := eq24301 X1
       grind)
    | exact superpose eq24301 eq75615
    | exact resolve eq75615 eq24301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24301 eq75615
  have eq76391 : ∀ X1 : G, (M.op X1 y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq76012 X1 x
       have i₂ := eq75324 X1 x
       grind)
    | exact superpose eq75324 eq76012
    | exact resolve eq76012 eq75324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75324 eq76012
  have eq76392 : ∀ X1 : G, (M.op X1 y) = (M.op (σ y) X1) := by
    intro X1
    first
    | (have i₁ := eq76016 X1 x
       have i₂ := eq75325 X1 x
       grind)
    | exact superpose eq75325 eq76016
    | exact resolve eq76016 eq75325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75325 eq76016
  have eq105961 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq76391 (σ x)
       grind)
    | exact superpose eq76391 eq14
    | exact resolve eq14 eq76391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76391
  have eq106012 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq105961
       have i₂ := eq75223 (σ x)
       grind)
    | exact superpose eq75223 eq105961
    | exact resolve eq105961 eq75223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105961
  have eq1963156 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 y) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq24157 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24157
  have eq2049760 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1963156 (σ y) x
       have i₂ := eq76392 x
       grind)
    | exact superpose eq76392 eq1963156
    | (have r₁ := eq1963156 (σ y) x
       have r₂ := eq76392 x
       grind)
    | exact resolve eq1963156 eq76392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76392
  have eq2049788 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq1963156 y X0
       have i₂ := eq75223 X0
       grind)
    | (have i₁ := eq1963156 X0 y
       have i₂ := eq75223 X0
       grind)
    | exact superpose eq75223 eq1963156
    | (have r₁ := eq1963156 y X0
       have r₂ := eq75223 X0
       grind)
    | (have r₁ := eq1963156 y y
       have r₂ := eq75223 y
       grind)
    | exact resolve eq1963156 eq75223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963156
  have eq2049798 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq2049788 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049788
  have eq2049812 : ∀ X0 : G, (M.op X0 y) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq2049760 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049760
  have eq2056382 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq2049812 (σ X0)
       grind)
    | exact superpose eq2049812 eq13
    | exact resolve eq13 eq2049812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049812
  have eq2056545 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2056382 X0
       have i₂ := eq75223 (σ X0)
       grind)
    | exact superpose eq75223 eq2056382
    | exact resolve eq2056382 eq75223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75223 eq2056382
  have eq2056641 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq2056545 X0
       have i₂ := eq2049798 X0
       grind)
    | exact superpose eq2049798 eq2056545
    | exact resolve eq2056545 eq2049798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049798 eq2056545
  have eq2107199 : (M.op y (σ x)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq106012
       have i₂ := eq2056641 x
       grind)
    | exact superpose eq2056641 eq106012
    | (have r₁ := eq106012
       have r₂ := eq2056641 x
       grind)
    | exact resolve eq106012 eq2056641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106012 eq2056641
  have eq2107210 : False := by grind
  exact eq2107210
