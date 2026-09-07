import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- `Equation3321`: `x ◇ y = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation3321 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3321 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3321.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X0) X0 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq16
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  clear eq17
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq66 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X0 X1) X1
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X0 X1) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X2) X3 (M.op X0 X1)
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
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
  have eq104 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq118 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq104 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq104
    | exact resolve eq104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq176 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq118 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq118
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq118 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq118
  have eq288 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq744 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq10
    | (have j1 := eq34 X1 X0
       grind)
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq836 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
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
  have eq901 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq1617 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X2 (M.op (M.op X3 X0) X0)) ∨ (M.op X2 (M.op (M.op X3 X0) X0)) = (k (M.op X2 (M.op (M.op X3 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47 (M.op X2 (M.op (M.op X3 X0) X0)) (M.op X0 X1)
       have i₂ := eq69 X3 X0 X1 X2
       grind)
    | exact superpose eq69 eq47
    | (have j0 := eq47 (M.op X2 (M.op (M.op X3 X0) X0)) (M.op X0 X1)
       grind)
    | exact resolve eq47 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq69
  have eq1623 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X2 (M.op X3 X0)) ∨ (M.op X2 (M.op (M.op X3 X0) X0)) = (k (M.op X2 (M.op (M.op X3 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1617 X0 X1 X2 X3
       have i₂ := eq66 X3 X0 X2
       grind)
    | exact superpose eq66 eq1617
    | (have j0 := eq1617 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1617 X1 X1 (M.op X1 X1) X1
       have r₂ := eq66 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq1617 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq1655 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X2 (M.op X3 X0)) ∨ (M.op X2 (M.op X3 X0)) = (k (M.op X2 (M.op X3 X0)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1623 X1 X1 X2 X0
       have i₂ := eq66 X0 X1 X2
       grind)
    | exact superpose eq66 eq1623
    | (have j0 := eq1623 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1623 X1 X1 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq66 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq1623 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1623
  have eq2419 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | (have j0 := eq74 X1 (σ X0)
       grind)
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq2491 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2419 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2419
    | (have j0 := eq2419 X0 X1
       grind)
    | exact resolve eq2419 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419
  have eq6571 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq288 x y
       grind)
    | exact superpose eq288 eq14
    | (have j1 := eq288 x y
       grind)
    | exact resolve eq14 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq6793 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq6571
       have i₂ := eq901 x y
       grind)
    | exact superpose eq901 eq6571
    | (have j1 := eq901 x y
       grind)
    | (have r₁ := eq6571
       have r₂ := eq901 x y
       grind)
    | exact resolve eq6571 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq6571
  have eq6797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by grind
  clear eq6793
  have eq6798 : y = (k y x) := by grind
  clear eq6797
  have eq6931 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq836 x y
       have i₂ := eq6798
       grind)
    | exact superpose eq6798 eq836
    | (have j0 := eq836 x y
       grind)
    | exact resolve eq836 eq6798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq21735 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq777 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq21736 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21735 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21735
    | (have j0 := eq21735 X0
       grind)
    | exact resolve eq21735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21735
  have eq22350 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq21736 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq21736
    | (have j0 := eq21736 (σ X0)
       grind)
    | exact resolve eq21736 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21736
  have eq22363 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22350 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq22350
    | (have j0 := eq22350 X0
       grind)
    | exact resolve eq22350 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22350
  have eq23174 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq22363 X0
       have i₂ := eq2491 X0 X0
       grind)
    | exact superpose eq2491 eq22363
    | (have j0 := eq22363 X0
       have j1 := eq2491 X0 X0
       grind)
    | (have r₁ := eq22363 x
       have r₂ := eq2491 x x
       grind)
    | exact resolve eq22363 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491 eq22363
  have eq23188 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23174 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23174
  have eq24046 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (M.op X0 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq23188 X0
       grind)
    | exact superpose eq23188 eq13
    | (have j1 := eq23188 X0
       grind)
    | exact resolve eq13 eq23188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23188
  have eq24147 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (M.op X0 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24046 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq24046
    | (have j0 := eq24046 X0 X1
       grind)
    | exact resolve eq24046 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24046
  have eq153317 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1655 X0 X0 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq153318 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq153317 x
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq153317
    | exact resolve eq153317 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153317
  have eq153338 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq153318 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq153318 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq153318
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq153318 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153318
  have eq187631 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq24147 X0 X0
       have i₂ := eq153338 X0 X0
       grind)
    | exact superpose eq153338 eq24147
    | (have j0 := eq24147 X0 x
       have j1 := eq153338 X0 X0
       grind)
    | exact resolve eq24147 eq153338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24147 eq153338
  have eq187676 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq187631 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187631
  have eq187717 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0)
       have i₂ := eq187676 X0
       grind)
    | exact superpose eq187676 eq9
    | (have j1 := eq187676 X0
       grind)
    | exact resolve eq9 eq187676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187676
  have eq187731 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq187717 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq187717
    | (have j0 := eq187717 X0
       grind)
    | exact resolve eq187717 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187717
  have eq187732 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq187731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187731
  have eq188148 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq187732 (σ X0)
       grind)
    | exact superpose eq187732 eq13
    | exact resolve eq13 eq187732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188279 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq188148 X0
       have i₂ := eq187732 X0
       grind)
    | exact superpose eq187732 eq188148
    | exact resolve eq188148 eq187732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187732 eq188148
  have eq189107 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq188279 X0
       grind)
    | exact superpose eq188279 eq176
    | (have j0 := eq176 X0 X1
       grind)
    | exact resolve eq176 eq188279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq189277 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1 (σ X0)
       have i₂ := eq188279 X0
       grind)
    | exact superpose eq188279 eq8
    | exact resolve eq8 eq188279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189424 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq189107 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq189107
    | (have j0 := eq189107 X0 X1
       grind)
    | exact resolve eq189107 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189107
  have eq193184 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq189424 y x
       grind)
    | exact superpose eq189424 eq14
    | (have j1 := eq189424 y x
       grind)
    | exact resolve eq14 eq189424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189424
  have eq193238 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq193184
       have i₂ := eq6798
       grind)
    | exact superpose eq6798 eq193184
    | exact resolve eq193184 eq6798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6798 eq193184
  have eq193334 : (σ y) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq193238
       have i₂ := eq6931
       grind)
    | exact superpose eq6931 eq193238
    | (have r₁ := eq193238
       have r₂ := eq6931
       grind)
    | exact resolve eq193238 eq6931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6931 eq193238
  have eq193336 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq193334
  have eq193337 : x = (M.op y y) := by grind
  clear eq193336
  have eq193504 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq189277 y X0
       have i₂ := eq193337
       grind)
    | exact superpose eq193337 eq189277
    | exact resolve eq189277 eq193337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189277
  have eq193509 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq19 y x y
       have i₂ := eq193337
       grind)
    | exact superpose eq193337 eq19
    | exact resolve eq19 eq193337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq194265 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq193509 y
       have i₂ := eq193337
       grind)
    | exact superpose eq193337 eq193509
    | exact resolve eq193509 eq193337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193509
  have eq200089 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ x) (σ y) X0
       have i₂ := eq193504 X0
       grind)
    | exact superpose eq193504 eq8
    | exact resolve eq8 eq193504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193504
  have eq206447 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq200089 (σ y)
       have i₂ := eq188279 y
       grind)
    | exact superpose eq188279 eq200089
    | exact resolve eq200089 eq188279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200089
  have eq206554 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq206447
       have i₂ := eq193337
       grind)
    | exact superpose eq193337 eq206447
    | exact resolve eq206447 eq193337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193337 eq206447
  have eq206557 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq206554
       have i₂ := eq188279 x
       grind)
    | exact superpose eq188279 eq206554
    | exact resolve eq206554 eq188279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188279 eq206554
  have eq206580 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq206557
       grind)
    | exact superpose eq206557 eq14
    | exact resolve eq14 eq206557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206557
  have eq206705 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq206580
       have i₂ := eq194265
       grind)
    | exact superpose eq194265 eq206580
    | exact resolve eq206580 eq194265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194265 eq206580
  have eq206706 : False := by grind
  exact eq206706

/-- `Equation333`: `x ◇ y = y ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation333 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law333 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law333.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X1)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  clear eq16
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq27 (τ X1) X0
       grind)
    | exact superpose eq27 eq18
    | (have j1 := eq27 (τ X1) X0
       grind)
    | exact resolve eq18 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 (σ X1) (σ X0)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq37
  have eq108 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq93
    | exact resolve eq93 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq147 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x y
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq216 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq45 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq45
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq41 (σ X1) X0
       grind)
    | exact superpose eq41 eq23
    | (have j1 := eq41 (σ X1) X1
       grind)
    | exact resolve eq23 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq791 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  clear eq32
  have eq863 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq791 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq791
    | (have j0 := eq791 X0 X1
       grind)
    | exact resolve eq791 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq951 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59
    | exact resolve eq59 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq994 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq951 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq951
    | (have j0 := eq951 X0 X1
       grind)
    | exact resolve eq951 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1415 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq8
    | (have j1 := eq56 X0 X1
       grind)
    | exact resolve eq8 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1805 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq159
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq159
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq159 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1806 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq159
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq159
    | (have j1 := eq41 y x
       grind)
    | exact resolve eq159 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1807 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq159
       have i₂ := eq994 y x
       grind)
    | exact superpose eq994 eq159
    | (have j1 := eq994 y x
       grind)
    | (have r₁ := eq159
       have r₂ := eq994 y x
       grind)
    | exact resolve eq159 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1808 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq159
       have i₂ := eq863 y x
       grind)
    | exact superpose eq863 eq159
    | (have j1 := eq863 (σ y) (σ x)
       grind)
    | (have r₁ := eq159
       have r₂ := eq863 y x
       grind)
    | exact resolve eq159 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq863
  have eq1809 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1808
  have eq1810 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq1807
  have eq1811 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq1806
  have eq1812 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1805
  have eq1832 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45 (σ x) (σ x)
       have i₂ := eq1811
       grind)
    | exact superpose eq1811 eq45
    | exact resolve eq45 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1811
  have eq1838 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1832
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq1832
    | exact resolve eq1832 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832
  have eq1991 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq2339 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq147
    | (have j0 := eq147 X1 (τ X0)
       grind)
    | exact resolve eq147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq2457 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2339 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2339
    | (have j0 := eq2339 X0 X1
       grind)
    | exact resolve eq2339 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2339
  have eq2475 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2457 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2457
    | (have j0 := eq2457 X0 X1
       grind)
    | exact resolve eq2457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq2498 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq1838
       grind)
    | exact superpose eq1838 eq9
    | exact resolve eq9 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq2546 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2498
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2498
    | exact resolve eq2498 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498
  have eq2547 : y = (k y y) := by
    first
    | (have j1 := eq62 y y
       grind)
    | (have r₁ := eq2546
       have r₂ := eq62 y y
       grind)
    | exact resolve eq2546 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2546
  have eq2809 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq164 y y
       have i₂ := eq2547
       grind)
    | exact superpose eq2547 eq164
    | (have j0 := eq164 y y
       grind)
    | exact resolve eq164 eq2547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq2547
  have eq2811 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2809
  have eq4696 : x = (k x (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108 x
       have i₂ := eq1812
       grind)
    | exact superpose eq1812 eq108
    | exact resolve eq108 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4703 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq4704 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1812
       grind)
    | exact superpose eq1812 eq8
    | exact resolve eq8 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4714 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4703
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq4703
    | exact resolve eq4703 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4703
  have eq4717 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4696
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4696
    | exact resolve eq4696 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4696
  have eq5080 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq4717
       grind)
    | exact superpose eq4717 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq4717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5085 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5080
  have eq5583 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq5085
  have eq7182 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4714
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq4714
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq4714 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4714
  have eq7247 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq7182
  have eq8534 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq108 x
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq108
    | exact resolve eq108 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8544 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq8
    | exact resolve eq8 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq8558 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8534
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8534
    | exact resolve eq8534 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8534
  have eq9039 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq8558
       grind)
    | exact superpose eq8558 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq8558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8558
  have eq9048 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9039
  have eq11901 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq108 x
       have i₂ := eq1810
       grind)
    | exact superpose eq1810 eq108
    | exact resolve eq108 eq1810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1810
  have eq11930 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11901
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq11901
    | exact resolve eq11901 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11901
  have eq11931 : x = (k x y) := by grind
  clear eq11930
  have eq11969 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1991 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq1991
    | (have j0 := eq1991 (τ X0) (τ X1)
       grind)
    | exact resolve eq1991 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq12030 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11969 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq11969
    | (have j0 := eq11969 X0 X1
       grind)
    | exact resolve eq11969 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11969
  have eq12041 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12030 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq12030
    | (have j0 := eq12030 X0 X1
       grind)
    | exact resolve eq12030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12030
  have eq12046 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12041 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12041
    | (have j0 := eq12041 X0 X1
       grind)
    | exact resolve eq12041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12041
  have eq12047 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12046 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12046
    | (have j0 := eq12046 X0 X1
       grind)
    | exact resolve eq12046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12046
  have eq12063 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1991 x y
       have i₂ := eq11931
       grind)
    | exact superpose eq11931 eq1991
    | (have j0 := eq1991 x y
       grind)
    | exact resolve eq1991 eq11931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq12346 : x ≠ y ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12047 x y
       have i₂ := eq4717
       grind)
    | exact superpose eq4717 eq12047
    | (have j0 := eq12047 x y
       grind)
    | exact resolve eq12047 eq4717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4717 eq12047
  have eq12355 : x ≠ y ∨ y = (M.op x y) := by grind
  clear eq12346
  have eq12465 : x = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq11931
       have i₂ := eq2475 x y
       grind)
    | exact superpose eq2475 eq11931
    | (have j1 := eq2475 x y
       grind)
    | exact resolve eq11931 eq2475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2475 eq11931
  have eq12586 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12465
       have r₂ := eq5583
       grind)
    | exact resolve eq12465 eq5583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5583 eq12465
  have eq15105 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4704
       grind)
    | exact superpose eq4704 eq14
    | exact resolve eq14 eq4704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4704
  have eq15510 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15105
       have i₂ := eq7247
       grind)
    | exact superpose eq7247 eq15105
    | exact resolve eq15105 eq7247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7247 eq15105
  have eq15512 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq15510
  have eq16961 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq280 (σ x) x
       have i₂ := eq1812
       grind)
    | exact superpose eq1812 eq280
    | exact resolve eq280 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq1812
  have eq17170 : (τ (σ y)) = (k (τ (σ x)) x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16961
       have r₂ := eq15512
       grind)
    | exact resolve eq16961 eq15512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15512 eq16961
  have eq17205 : (k x x) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17170
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq17170
    | exact resolve eq17170 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17170
  have eq17214 : y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17205
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq17205
    | exact resolve eq17205 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17205
  have eq17252 : y = (M.op x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq216 x x
       have i₂ := eq17214
       grind)
    | exact superpose eq17214 eq216
    | exact resolve eq216 eq17214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq17214
  have eq17260 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17252
       have r₂ := eq12355
       grind)
    | exact resolve eq17252 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17252
  have eq17533 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9048
       have i₂ := eq17260
       grind)
    | exact superpose eq17260 eq9048
    | exact resolve eq9048 eq17260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9048 eq17260
  have eq17542 : y = (M.op x x) ∨ x = y := by grind
  clear eq17533
  have eq17833 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq17542
       grind)
    | exact superpose eq17542 eq8
    | exact resolve eq8 eq17542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17542
  have eq17840 : y = (M.op x y) := by
    first
    | (have r₁ := eq17833
       have r₂ := eq12355
       grind)
    | exact resolve eq17833 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12355 eq17833
  have eq19794 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq8544
       grind)
    | exact superpose eq8544 eq14
    | exact resolve eq14 eq8544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8544
  have eq19823 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19794
       have i₂ := eq17840
       grind)
    | exact superpose eq17840 eq19794
    | exact resolve eq19794 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19794
  have eq19824 : y = (M.op x x) := by grind
  clear eq19823
  have eq20553 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1415 x x
       have i₂ := eq12586
       grind)
    | exact superpose eq12586 eq1415
    | exact resolve eq1415 eq12586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq12586
  have eq20635 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20553
       have r₂ := eq12063
       grind)
    | exact resolve eq20553 eq12063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12063 eq20553
  have eq20649 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq20635
       have i₂ := eq17840
       grind)
    | exact superpose eq17840 eq20635
    | exact resolve eq20635 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20635
  have eq20666 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq20649
       grind)
    | exact superpose eq20649 eq14
    | exact resolve eq14 eq20649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20649
  have eq20705 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20666
       have i₂ := eq17840
       grind)
    | exact superpose eq17840 eq20666
    | exact resolve eq20666 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17840 eq20666
  have eq20706 : x = y := by grind
  clear eq20705
  have eq21176 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20706
       grind)
    | exact superpose eq20706 eq14
    | exact resolve eq14 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21189 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2811
       have i₂ := eq20706
       grind)
    | exact superpose eq20706 eq2811
    | exact resolve eq2811 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811
  have eq21234 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21176
       have i₂ := eq19824
       grind)
    | exact superpose eq19824 eq21176
    | exact resolve eq21176 eq19824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19824 eq21176
  have eq21235 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq21234
       have i₂ := eq21189
       grind)
    | exact superpose eq21189 eq21234
    | exact resolve eq21234 eq21189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21189 eq21234
  have eq21236 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq21235
       have i₂ := eq20706
       grind)
    | exact superpose eq20706 eq21235
    | exact resolve eq21235 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20706 eq21235
  have eq21237 : False := by grind
  exact eq21237

/-- `Equation3343`: `x ◇ y = y ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3343 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3343 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3343.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
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
  have eq19 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op X0 X0)
       have i₂ := eq8 X0 X0
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  clear eq28
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq24
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X0 (M.op X1 X0)
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq38
  have eq104 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq90
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq178 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
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
  have eq190 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq30 X0 X2
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 X0 X2
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X0
       have i₂ := eq58 (σ X0) X1
       grind)
    | (have i₁ := eq30 X0 X1
       have i₂ := eq58 (σ X1) (σ X0)
       grind)
    | exact superpose eq58 eq30
    | (have j1 := eq58 (σ X1) X0
       grind)
    | exact resolve eq30 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq732 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq810 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq732 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq732
    | (have j0 := eq732 X0 X1
       grind)
    | exact resolve eq732 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq872 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  clear eq810
  have eq1296 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq41 x y
       grind)
    | exact superpose eq41 eq14
    | (have j1 := eq41 x y
       grind)
    | exact resolve eq14 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1300 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
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
  clear eq41
  have eq1696 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq190
       have i₂ := eq872 y x
       grind)
    | exact superpose eq872 eq190
    | (have j1 := eq872 y x
       grind)
    | (have r₁ := eq190
       have r₂ := eq872 y x
       grind)
    | exact resolve eq190 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq872
  have eq1699 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq1696
  have eq2348 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq104 x
       have i₂ := eq1699
       grind)
    | exact superpose eq1699 eq104
    | exact resolve eq104 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1699
  have eq2380 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2348
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2348
    | exact resolve eq2348 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq2381 : x = (k x y) := by grind
  clear eq2380
  have eq5546 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq200
    | exact resolve eq200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq5707 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5546 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq5546
    | (have j0 := eq5546 X0 X1 X2
       grind)
    | exact resolve eq5546 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5546
  have eq47278 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5707 X2 (τ X1) (τ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq5707
    | (have j0 := eq5707 X2 (τ X1) X2
       grind)
    | exact resolve eq5707 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq5707
  have eq47890 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47278 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47278
    | (have j0 := eq47278 X0 X1 X2
       grind)
    | exact resolve eq47278 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47278
  have eq47947 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47890 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq47890
    | (have j0 := eq47890 X0 X1 X2
       grind)
    | exact resolve eq47890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47890
  have eq47951 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (k X0 X1) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47947 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47947
    | (have j0 := eq47947 X0 X1 X2
       grind)
    | exact resolve eq47947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47947
  have eq70468 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq70534 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq70468 X0 X1
       have j1 := eq178 X1 X0
       grind)
    | (have r₁ := eq70468 (k X1 X1) X0
       have r₂ := eq178 X0 X1
       grind)
    | (have r₁ := eq70468 X0 (σ (k X1 X1))
       have r₂ := eq178 (σ X0) X1
       grind)
    | (have r₁ := eq70468 X1 X0
       have r₂ := eq178 X0 X1
       grind)
    | exact resolve eq70468 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq70468
  have eq70583 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq70534 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq70534 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq70534 eq16
    | (have j1 := eq70534 (τ X1) X0
       grind)
    | exact resolve eq16 eq70534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq70584 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq70534 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq70534 X0 (σ X0)
       grind)
    | exact superpose eq70534 eq9
    | (have j1 := eq70534 X1 X0
       grind)
    | exact resolve eq9 eq70534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70534
  have eq70629 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq70583 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq70583
    | (have j0 := eq70583 X0 X1
       grind)
    | exact resolve eq70583 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70583
  have eq70638 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70629 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70629
    | (have j0 := eq70629 X0 X1
       grind)
    | exact resolve eq70629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70629
  have eq71190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1296
       have i₂ := eq70638 y x
       grind)
    | exact superpose eq70638 eq1296
    | (have j1 := eq70638 y x
       grind)
    | exact resolve eq1296 eq70638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296 eq70638
  have eq71326 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq71190
  have eq80343 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq70584 (σ X1) X0
       grind)
    | exact superpose eq70584 eq13
    | (have j1 := eq70584 (σ X1) X0
       grind)
    | exact resolve eq13 eq70584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70584
  have eq80362 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80343 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq80343
    | (have j0 := eq80343 X0 X1
       grind)
    | exact resolve eq80343 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80343
  have eq84314 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq80362 x y
       grind)
    | exact superpose eq80362 eq14
    | (have j1 := eq80362 x y
       grind)
    | exact resolve eq14 eq80362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80362
  have eq84364 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq84314
       have i₂ := eq2381
       grind)
    | exact superpose eq2381 eq84314
    | exact resolve eq84314 eq2381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381 eq84314
  have eq84383 : y = (k x x) := by
    first
    | (have r₁ := eq84364
       have r₂ := eq71326
       grind)
    | exact resolve eq84364 eq71326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71326 eq84364
  have eq119407 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq312
    | exact resolve eq312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq120345 : ∀ X0 X1 : G, (M.op X1 X0) = (k (σ (τ X0)) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq119407 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq119407
    | (have j0 := eq119407 X0 X1
       grind)
    | exact resolve eq119407 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq119407
  have eq120347 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq120345 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120345
    | (have j0 := eq120345 X0 X1
       grind)
    | exact resolve eq120345 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120345
  have eq165771 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47951 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47951
  have eq165772 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq165771
  have eq165783 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq165772 X0 X0
       have i₂ := eq58 X0 X1
       grind)
    | (have i₁ := eq165772 X1 X0
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq165772
    | (have j0 := eq165772 X0 X1
       have j1 := eq58 X1 X0
       grind)
    | (have r₁ := eq165772 (M.op X0 X0) X0
       have r₂ := eq58 X0 (M.op X0 X0)
       grind)
    | exact resolve eq165772 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq165772
  have eq165958 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq165783 X0 X1
       have j1 := eq120347 X1 X0
       grind)
    | (have r₁ := eq165783 X1 X0
       have r₂ := eq120347 X0 X1
       grind)
    | exact resolve eq165783 eq120347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120347 eq165783
  have eq178572 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq165958 x x
       have i₂ := eq84383
       grind)
    | exact superpose eq84383 eq165958
    | exact resolve eq165958 eq84383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84383
  have eq178713 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq165958 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165958
  have eq178714 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq178713 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178713
  have eq178716 : y = (M.op x x) := by grind
  clear eq178572
  have eq179096 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq178714 (σ X0)
       grind)
    | exact superpose eq178714 eq13
    | exact resolve eq13 eq178714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179176 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq179096 X0
       have i₂ := eq178714 X0
       grind)
    | exact superpose eq178714 eq179096
    | exact resolve eq179096 eq178714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178714 eq179096
  have eq183834 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0)
       have i₂ := eq179176 X0
       grind)
    | exact superpose eq179176 eq19
    | exact resolve eq19 eq179176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183931 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq183834 X0
       have i₂ := eq179176 (M.op X0 X0)
       grind)
    | exact superpose eq179176 eq183834
    | exact resolve eq183834 eq179176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179176 eq183834
  have eq184008 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq183931 X0
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq183931
    | exact resolve eq183931 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq183931
  have eq208360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184008 x
       have i₂ := eq178716
       grind)
    | exact superpose eq178716 eq184008
    | exact resolve eq184008 eq178716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178716 eq184008
  have eq208409 : False := by grind
  exact eq208409

/-- `Equation3343`: `x ◇ y = y ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation3343 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3343 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3343.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
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
  have eq19 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op X0 X0)
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq29 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq26
    | exact resolve eq26 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq60 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 (M.op X1 X0) X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq28 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq14
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq61 (σ X1) (σ X0)
       grind)
    | (have i₁ := eq28 X0 X0
       have i₂ := eq61 (σ X0) X1
       grind)
    | exact superpose eq61 eq28
    | (have j1 := eq61 (σ X1) X0
       grind)
    | exact resolve eq28 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq737 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq815 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq737 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq737
    | (have j0 := eq737 X0 X1
       grind)
    | exact resolve eq737 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq877 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  clear eq815
  have eq1302 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
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
  have eq1306 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq41 X0 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq41 X0 X0
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1707 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq192
       have i₂ := eq877 y x
       grind)
    | exact superpose eq877 eq192
    | (have j1 := eq877 y x
       grind)
    | (have r₁ := eq192
       have r₂ := eq877 y x
       grind)
    | exact resolve eq192 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq877
  have eq1710 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by grind
  clear eq1707
  have eq2362 : x = (k (τ (σ y)) x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq60 x
       have i₂ := eq1710
       grind)
    | exact superpose eq1710 eq60
    | exact resolve eq60 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1710
  have eq2394 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq2362
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2362
    | exact resolve eq2362 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq2395 : x = (k y x) := by grind
  clear eq2394
  have eq5354 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq201
    | exact resolve eq201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq5508 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5354 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq5354
    | (have j0 := eq5354 X0 X1 X2
       grind)
    | exact resolve eq5354 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5354
  have eq46327 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5508 X2 (τ X0) (τ X1)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq5508
    | (have j0 := eq5508 X2 (τ X0) X2
       grind)
    | exact resolve eq5508 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq5508
  have eq46934 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46327 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq46327
    | (have j0 := eq46327 X0 X1 X2
       grind)
    | exact resolve eq46327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46327
  have eq46991 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46934 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq46934
    | (have j0 := eq46934 X0 X1 X2
       grind)
    | exact resolve eq46934 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46934
  have eq46995 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (k (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46991 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46991
    | (have j0 := eq46991 X0 X1 X2
       grind)
    | exact resolve eq46991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46991
  have eq85999 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq86079 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq85999 X0 X1
       have j1 := eq180 X1 X0
       grind)
    | (have r₁ := eq85999 (k X1 X1) X0
       have r₂ := eq180 X0 X1
       grind)
    | (have r₁ := eq85999 X0 (σ (k X1 X1))
       have r₂ := eq180 (σ X0) X1
       grind)
    | (have r₁ := eq85999 X1 X0
       have r₂ := eq180 X0 X1
       grind)
    | exact resolve eq85999 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq85999
  have eq86857 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq86079 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq86079 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq86079 eq16
    | (have j1 := eq86079 (τ X1) X0
       grind)
    | exact resolve eq16 eq86079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq86869 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq86079 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq86079 X0 (σ X0)
       grind)
    | exact superpose eq86079 eq9
    | (have j1 := eq86079 X1 X0
       grind)
    | exact resolve eq9 eq86079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86079
  have eq87222 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq86857 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq86857
    | (have j0 := eq86857 X0 X1
       grind)
    | exact resolve eq86857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86857
  have eq87298 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87222 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87222
    | (have j0 := eq87222 X0 X1
       grind)
    | exact resolve eq87222 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87222
  have eq88321 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1302
       have i₂ := eq87298 y x
       grind)
    | exact superpose eq87298 eq1302
    | (have j1 := eq87298 y x
       grind)
    | exact resolve eq1302 eq87298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302 eq87298
  have eq88536 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq88321
  have eq102714 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq86869 (σ X1) X0
       grind)
    | exact superpose eq86869 eq13
    | (have j1 := eq86869 (σ X1) X0
       grind)
    | exact resolve eq13 eq86869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86869
  have eq102813 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq102714 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq102714
    | (have j0 := eq102714 X0 X1
       grind)
    | exact resolve eq102714 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102714
  have eq130929 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq102813 x y
       grind)
    | exact superpose eq102813 eq14
    | (have j1 := eq102813 x y
       grind)
    | exact resolve eq14 eq102813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102813
  have eq131126 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq130929
       have i₂ := eq2395
       grind)
    | exact superpose eq2395 eq130929
    | exact resolve eq130929 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395 eq130929
  have eq131287 : y = (k x x) := by
    first
    | (have r₁ := eq131126
       have r₂ := eq88536
       grind)
    | exact resolve eq131126 eq88536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88536 eq131126
  have eq176617 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (k (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq321
    | exact resolve eq321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq177558 : ∀ X0 X1 : G, (M.op X1 X0) = (k (σ (τ X0)) X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176617 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq176617
    | (have j0 := eq176617 X0 X1
       grind)
    | exact resolve eq176617 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq176617
  have eq177560 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177558 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177558
    | (have j0 := eq177558 X0 X1
       grind)
    | exact resolve eq177558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177558
  have eq296585 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46995 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46995
  have eq296586 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq296585
  have eq297566 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq296586 X0 X1
       have i₂ := eq61 X0 X1
       grind)
    | (have i₁ := eq296586 X0 X0
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq296586
    | (have j0 := eq296586 X1 X0
       have j1 := eq61 X1 X0
       grind)
    | (have r₁ := eq296586 X0 (M.op X0 X0)
       have r₂ := eq61 X0 (M.op X0 X0)
       grind)
    | exact resolve eq296586 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq296586
  have eq297789 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq297566 X0 X1
       have j1 := eq177560 X1 X0
       grind)
    | (have r₁ := eq297566 X1 X0
       have r₂ := eq177560 X0 X1
       grind)
    | exact resolve eq297566 eq177560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177560 eq297566
  have eq334135 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq297789 x x
       have i₂ := eq131287
       grind)
    | exact superpose eq131287 eq297789
    | exact resolve eq297789 eq131287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131287
  have eq334323 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq297789 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297789
  have eq334324 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq334323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334323
  have eq334326 : y = (M.op x x) := by grind
  clear eq334135
  have eq339102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq334324 (σ X0)
       grind)
    | exact superpose eq334324 eq13
    | exact resolve eq13 eq334324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339188 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq339102 X0
       have i₂ := eq334324 X0
       grind)
    | exact superpose eq334324 eq339102
    | exact resolve eq339102 eq334324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334324 eq339102
  have eq351018 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0)
       have i₂ := eq339188 X0
       grind)
    | exact superpose eq339188 eq19
    | exact resolve eq19 eq339188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351128 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq351018 X0
       have i₂ := eq339188 (M.op X0 X0)
       grind)
    | exact superpose eq339188 eq351018
    | exact resolve eq351018 eq339188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339188 eq351018
  have eq351224 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq351128 X0
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq351128
    | exact resolve eq351128 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq351128
  have eq466173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq351224 x
       have i₂ := eq334326
       grind)
    | exact superpose eq334326 eq351224
    | exact resolve eq351224 eq334326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334326 eq351224
  have eq466235 : False := by grind
  exact eq466235
