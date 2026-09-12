import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2588`: `x = (y ◇ ((z ◇ y) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxx_pxy_pyx_Equation2588 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2588 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2588.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X0) = X0 := by
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
  have eq176 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq16 X3 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq176 X0 (M.op X0 X0)
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1038 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1039 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1095 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1095 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1095 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1135 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq1105 (M.op X0 X0)
       grind)
    | exact superpose eq1105 eq199
    | exact resolve eq199 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq1148 : ∀ X0 X1 : G, (M.op (k (k X0 X0) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1135 X0 X1
       have i₂ := eq1105 X0
       grind)
    | exact superpose eq1105 eq1135
    | exact resolve eq1135 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1668 : ∀ X0 X1 : G, (M.op (k (σ (k X0 X0)) (σ (k X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1148 (σ X1) X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq1148
    | exact resolve eq1148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1725 : ∀ X0 X1 : G, (M.op (σ (k (k X0 X0) (k X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1668 X0 X1
       have i₂ := eq10 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10 eq1668
    | exact resolve eq1668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq4141 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1038
       grind)
    | exact superpose eq1038 eq39
    | exact resolve eq39 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq4142 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4141
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4141
    | exact resolve eq4141 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4141
  have eq4144 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq4142
    | exact resolve eq4142 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4142
  have eq4146 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq4144
       have i₂ := eq1105 x
       grind)
    | exact superpose eq1105 eq4144
    | exact resolve eq4144 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144
  have eq88039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4146 eq1039
    | exact resolve eq1039 eq4146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88048 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq88039
       have r₂ := eq27
       grind)
    | exact resolve eq88039 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88039
  have eq88055 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq88048
       have i₂ := eq1105 sF2
       grind)
    | exact superpose eq1105 eq88048
    | exact resolve eq88048 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88048
  have eq88059 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq88055 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq88055
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq88055
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq88055
       grind)
    | exact resolve eq12 eq88055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88055
  have eq88085 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq88059
       have r₂ := eq26
       grind)
    | exact resolve eq88059 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88059
  have eq88091 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq88085
       have i₂ := eq1105 sF2
       grind)
    | exact superpose eq1105 eq88085
    | exact resolve eq88085 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88085
  have eq88092 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq88091
  have eq88097 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4146 eq88092
    | exact resolve eq88092 eq4146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4146 eq88092
  have eq88098 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq88097
       have r₂ := eq27
       grind)
    | exact resolve eq88097 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88097
  have eq88103 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq88098 eq141
    | exact resolve eq141 eq88098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88098
  have eq88310 : x = (k x x) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq29 eq88103
    | exact resolve eq88103 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88103
  have eq88311 : (M.op x y) = (M.op y x) ∨ x = (k x x) := by grind
  clear eq88310
  have eq88412 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq88311
       grind)
    | exact superpose eq88311 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq88311
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq88311
       grind)
    | exact resolve eq12 eq88311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88311
  have eq88438 : x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have r₁ := eq88412
       have r₂ := eq18
       grind)
    | exact resolve eq88412 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88412
  have eq88444 : x = (k x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq88438
       have i₂ := eq1105 x
       grind)
    | exact superpose eq1105 eq88438
    | exact resolve eq88438 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88438
  have eq88445 : (M.op x y) = (k y x) ∨ x = (k x x) := by grind
  clear eq88444
  have eq88453 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq88445
       grind)
    | exact superpose eq88445 eq39
    | exact resolve eq39 eq88445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88445
  have eq88455 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq88453
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq88453
    | exact resolve eq88453 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88453
  have eq88459 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq88455
    | exact resolve eq88455 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88455
  have eq88464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq88459 eq1039
    | exact resolve eq1039 eq88459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq88473 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq88464
       have r₂ := eq27
       grind)
    | exact resolve eq88464 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88464
  have eq88480 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq88473
       have i₂ := eq1105 sF2
       grind)
    | exact superpose eq1105 eq88473
    | exact resolve eq88473 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88473
  have eq88947 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq88480 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq88480
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq88480
       grind)
    | exact resolve eq12 eq88480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88480
  have eq88973 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq88947
       have r₂ := eq26
       grind)
    | exact resolve eq88947 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88947
  have eq88979 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq88973
       have i₂ := eq1105 sF2
       grind)
    | exact superpose eq1105 eq88973
    | exact resolve eq88973 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq88973
  have eq88980 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by grind
  clear eq88979
  have eq88985 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq88459 eq88980
    | exact resolve eq88980 eq88459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88459 eq88980
  have eq88986 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq88985
       have r₂ := eq27
       grind)
    | exact resolve eq88985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88985
  have eq88991 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) := by
    first
    | exact superpose eq88986 eq141
    | exact resolve eq141 eq88986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq88986
  have eq89198 : x = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq88991
    | exact resolve eq88991 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq88991
  have eq89199 : x = (k x x) := by grind
  clear eq89198
  have eq89301 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq89199
       grind)
    | exact superpose eq89199 eq39
    | exact resolve eq39 eq89199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89306 : ∀ X0 : G, (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1148 x x
       have i₂ := eq89199
       grind)
    | exact superpose eq89199 eq1148
    | exact resolve eq1148 eq89199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq89329 : ∀ X0 : G, (M.op (σ (k x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1725 x x
       have i₂ := eq89199
       grind)
    | exact superpose eq89199 eq1725
    | exact resolve eq1725 eq89199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq89485 : ∀ X0 : G, (M.op (k (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89329 X0
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq89329
    | exact resolve eq89329 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq89329
  have eq89505 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89306 X0
       have i₂ := eq89199
       grind)
    | exact superpose eq89199 eq89306
    | exact resolve eq89306 eq89199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89199 eq89306
  have eq89508 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq89301
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq89301
    | exact resolve eq89301 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89301
  have eq89582 : ∀ X0 : G, (M.op (k (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89485 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq89485
    | (have j0 := eq89485 X0
       grind)
    | exact resolve eq89485 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq89485
  have eq89651 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq89508 eq89582
    | exact resolve eq89582 eq89508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89508 eq89582
  have eq89729 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq89505 y
       grind)
    | exact superpose eq89505 eq18
    | (have j1 := eq89505 y
       grind)
    | exact resolve eq18 eq89505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq89505
  have eq90046 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq89729
       grind)
    | exact superpose eq89729 eq24
    | exact resolve eq24 eq89729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq89729
  have eq90227 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq90046 eq20
    | exact resolve eq20 eq90046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq90046
  have eq91327 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq89651 eq26
    | (have j1 := eq89651 (σ y)
       grind)
    | exact resolve eq26 eq89651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq89651
  have eq91648 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq91327 eq27
    | exact resolve eq27 eq91327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq91327
  have eq91741 : False := by grind
  exact eq91741

/-- `Equation2588`: `x = (y ◇ ((z ◇ y) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxx_pyx_Equation2588 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2588 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2588.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X0) = X0 := by
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
  have eq53 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq76 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq10
    | exact resolve eq10 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq44
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq80 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq50
    | exact resolve eq50 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq81 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq80
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq80
    | exact resolve eq80 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq82 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq79
    | exact resolve eq79 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq78 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq78
    | exact resolve eq78 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq78
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq432 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq53
    | exact resolve eq53 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1264 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq432 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq53 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq53 eq432
    | exact resolve eq432 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq1325 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1264 X0 X1
       have i₂ := eq83 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq83 eq1264
    | exact resolve eq1264 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1264
  have eq1345 : ∀ X0 X1 : G, (M.op (σ (M.op X0 (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1325 X0 X1
       have i₂ := eq53 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have i₁ := eq1325 X0 X1
       have i₂ := eq53 X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq53 eq1325
    | exact resolve eq1325 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq38282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq38283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq38282
    | exact resolve eq38282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38282
  have eq38295 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq38283
       have r₂ := eq28
       grind)
    | exact resolve eq38283 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38283
  have eq38299 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq38295 eq81
    | exact resolve eq81 eq38295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38295
  have eq38391 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq38299
    | exact resolve eq38299 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38299
  have eq38392 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38391
  have eq38398 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq82
       have i₂ := eq38392
       grind)
    | exact superpose eq38392 eq82
    | exact resolve eq82 eq38392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38406 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq38392
       grind)
    | exact superpose eq38392 eq53
    | exact resolve eq53 eq38392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq38426 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1345 x X0
       have i₂ := eq38392
       grind)
    | exact superpose eq38392 eq1345
    | exact resolve eq1345 eq38392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq38478 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38426 X0
       have i₂ := eq82
       grind)
    | exact superpose eq82 eq38426
    | exact resolve eq38426 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq38426
  have eq38492 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq38398
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38398
    | exact resolve eq38398 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38398
  have eq38718 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38406 X0
       have i₂ := eq38392
       grind)
    | exact superpose eq38392 eq38406
    | exact resolve eq38406 eq38392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38392 eq38406
  have eq38898 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38718
  have eq38941 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq38898 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq38898
    | (have j0 := eq38898 y
       grind)
    | exact resolve eq38898 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38898
  have eq39147 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38941 eq30
    | exact resolve eq30 eq38941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38941
  have eq39270 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq39147
    | exact resolve eq39147 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39147
  have eq39271 : y = (M.op x y) ∨ x = y := by grind
  clear eq39270
  have eq39434 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq39271 eq21
    | exact resolve eq21 eq39271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39271
  have eq39555 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39434
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39434
    | exact resolve eq39434 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39434
  have eq39571 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq39555 eq27
    | exact resolve eq27 eq39555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39555
  have eq59416 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq38492 eq38478
    | exact resolve eq38478 eq38492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38478 eq38492
  have eq59616 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq59416 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59416
  have eq59663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq59616 eq39571
    | exact resolve eq39571 eq59616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39571 eq59616
  have eq59829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq59663
  have eq59883 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq59829
       have r₂ := eq28
       grind)
    | exact resolve eq59829 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59829
  have eq59893 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq59883 eq30
    | exact resolve eq30 eq59883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq59883
  have eq60114 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq59893
    | exact resolve eq59893 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq59893
  have eq60115 : x = y := by grind
  clear eq60114
  have eq60130 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq60115
       grind)
    | exact superpose eq60115 eq19
    | exact resolve eq19 eq60115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq60131 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq60115
       grind)
    | exact superpose eq60115 eq25
    | exact resolve eq25 eq60115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq60115
  have eq60275 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq60131
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60131
    | exact resolve eq60131 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq60131
  have eq60295 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq60275 eq27
    | exact resolve eq27 eq60275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq60275
  have eq60643 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60295 eq81
    | exact resolve eq81 eq60295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq60295
  have eq60743 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq60643
       have i₂ := eq60130
       grind)
    | exact superpose eq60130 eq60643
    | exact resolve eq60643 eq60130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60130 eq60643
  have eq60752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60743 eq15
    | exact resolve eq15 eq60743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60743
  have eq60831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq60752
    | exact resolve eq60752 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq60752
  have eq60852 : False := by grind
  exact eq60852

/-- `Equation2646`: `x = ((x ◇ x) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation2646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2646.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq477 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq494 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq517 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq494 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq494
    | (have j0 := eq494 X0 X1
       grind)
    | exact resolve eq494 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq711 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq517 x y
       grind)
    | exact superpose eq517 eq16
    | (have j1 := eq517 x y
       grind)
    | exact resolve eq16 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq517 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq3177 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq491 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq491
    | exact resolve eq491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq3235 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3177 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3177
    | (have j0 := eq3177 X0 X1
       grind)
    | exact resolve eq3177 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177
  have eq6733 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq711
       have i₂ := eq3235 y x
       grind)
    | exact superpose eq3235 eq711
    | (have j1 := eq3235 y x
       grind)
    | (have r₁ := eq711
       have r₂ := eq3235 y x
       grind)
    | (have r₁ := eq711
       have r₂ := eq3235 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq711
       have r₂ := eq3235 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq711 eq3235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq3235
  have eq6734 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6733
  have eq6746 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq716 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq716
    | (have j0 := eq716 (τ X0) (τ X1)
       grind)
    | exact resolve eq716 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq6813 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6746 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6746
    | (have j0 := eq6746 X0 X1
       grind)
    | exact resolve eq6746 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746
  have eq6848 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6813 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq6813
    | (have j0 := eq6813 X0 X1
       grind)
    | exact resolve eq6813 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6813
  have eq6880 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6848 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6848
    | (have j0 := eq6848 X0 X1
       grind)
    | exact resolve eq6848 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6848
  have eq6906 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6880 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6880
    | (have j0 := eq6880 X0 X1
       grind)
    | exact resolve eq6880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6880
  have eq6925 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6906 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq6906
    | (have j0 := eq6906 X0 X1
       grind)
    | exact resolve eq6906 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6906
  have eq6942 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6925 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6925
    | (have j0 := eq6925 X0 X1
       grind)
    | exact resolve eq6925 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6925
  have eq6955 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6942 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6942
    | (have j0 := eq6942 X0 X1
       grind)
    | exact resolve eq6942 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6942
  have eq14954 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6734
       grind)
    | exact superpose eq6734 eq16
    | exact resolve eq16 eq6734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6734
  have eq14955 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq14954
       have r₂ := eq22 x
       grind)
    | exact resolve eq14954 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14954
  have eq14957 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq14955
       grind)
    | exact superpose eq14955 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14955
       grind)
    | exact resolve eq13 eq14955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14955
  have eq14959 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq14957
  have eq16573 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14959
       grind)
    | exact superpose eq14959 eq16
    | exact resolve eq16 eq14959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14959
  have eq16574 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq16573
       have r₂ := eq22 x
       grind)
    | exact resolve eq16573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16573
  have eq16577 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq477 x (σ y)
       have i₂ := eq16574
       grind)
    | exact superpose eq16574 eq477
    | (have j0 := eq477 x (σ y)
       grind)
    | (have r₁ := eq477 x (σ y)
       have r₂ := eq16574
       grind)
    | exact resolve eq477 eq16574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16574
  have eq16589 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq16577
  have eq16590 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq16589
  have eq16596 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16590
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16590
    | exact resolve eq16590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16590
  have eq16669 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq716 x y
       have i₂ := eq16596
       grind)
    | exact superpose eq16596 eq716
    | (have j0 := eq716 x y
       grind)
    | (have r₁ := eq716 x y
       have r₂ := eq16596
       grind)
    | exact resolve eq716 eq16596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16596
  have eq16697 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq16669
  have eq16698 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq16697
  have eq16703 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq716 x y
       grind)
    | (have r₁ := eq16698
       have r₂ := eq716 x y
       grind)
    | exact resolve eq16698 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq16698
  have eq16707 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16703
       grind)
    | exact superpose eq16703 eq16
    | exact resolve eq16 eq16703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16708 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq477 x (σ y)
       have i₂ := eq16703
       grind)
    | exact superpose eq16703 eq477
    | (have j0 := eq477 x (σ y)
       grind)
    | (have r₁ := eq477 x (σ y)
       have r₂ := eq16703
       grind)
    | exact resolve eq477 eq16703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq16703
  have eq16721 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq16708
  have eq16722 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq16721
  have eq16729 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16722
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16722
    | exact resolve eq16722 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16722
  have eq16741 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16729
       grind)
    | exact superpose eq16729 eq10
    | exact resolve eq10 eq16729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16729
  have eq16904 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16741
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16741
    | exact resolve eq16741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16741
  have eq16906 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16904
       grind)
    | exact superpose eq16904 eq16
    | exact resolve eq16 eq16904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16904
  have eq16907 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq16906
       have r₂ := eq22 x
       grind)
    | exact resolve eq16906 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16906
  have eq16921 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq16907
       grind)
    | exact superpose eq16907 eq10
    | exact resolve eq10 eq16907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16907
  have eq17085 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16921
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq16921
    | exact resolve eq16921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16921
  have eq17115 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq6955 x y
       have i₂ := eq17085
       grind)
    | exact superpose eq17085 eq6955
    | (have j0 := eq6955 x y
       grind)
    | (have r₁ := eq6955 x y
       have r₂ := eq17085
       grind)
    | exact resolve eq6955 eq17085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6955 eq17085
  have eq17118 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17115
  have eq17122 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16707
       have i₂ := eq17118
       grind)
    | exact superpose eq17118 eq16707
    | exact resolve eq16707 eq17118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16707 eq17118
  have eq17131 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq17122
  have eq17132 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17131
       grind)
    | exact superpose eq17131 eq16
    | exact resolve eq16 eq17131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17131
  have eq17135 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq17132
       have r₂ := eq22 x
       grind)
    | exact resolve eq17132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17132
  have eq17136 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17135
       grind)
    | exact superpose eq17135 eq16
    | exact resolve eq16 eq17135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17137 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17135
       grind)
    | exact superpose eq17135 eq10
    | exact resolve eq10 eq17135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17135
  have eq17300 : x = y := by
    first
    | (have i₁ := eq17137
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17137
    | exact resolve eq17137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17137
  have eq17301 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17136
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq17136
    | exact resolve eq17136 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17136
  have eq17302 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17301
       have i₂ := eq17300
       grind)
    | exact superpose eq17300 eq17301
    | exact resolve eq17301 eq17300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17300 eq17301
  have eq17303 : False := by grind
  exact eq17303

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyx_pxy_Equation2653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq23 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq59 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
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
  have eq63 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq59 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq76 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op X0 X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X1)) = (k X2 (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq63 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | (have j1 := eq63 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq63 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq108 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq108 (σ X0) (σ X1)
       grind)
    | exact superpose eq108 eq15
    | (have j1 := eq108 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq108 (τ X0) X1
       grind)
    | exact superpose eq108 eq17
    | (have j1 := eq108 (τ X0) X1
       grind)
    | exact resolve eq17 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq108
  have eq401 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq82 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq81 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq81 eq82
    | exact resolve eq82 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq402 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq82 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq402 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq402
    | exact resolve eq402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq413 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq401 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq401
    | exact resolve eq401 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq414 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq412 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq412
    | exact resolve eq412 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq415 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq414 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq414
    | exact resolve eq414 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq418 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq415 (M.op X0 X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq415
    | exact resolve eq415 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq426 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq418 X0
       have i₂ := eq415 X0
       grind)
    | exact superpose eq415 eq418
    | exact resolve eq418 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq533 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq413 X0
       grind)
    | exact superpose eq413 eq9
    | exact resolve eq9 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq413 X0
       grind)
    | exact superpose eq413 eq9
    | exact resolve eq9 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X1) = (M.op (M.op X0 (M.op X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq533 X0 X2
       have i₂ := eq533 X0 X1
       grind)
    | exact superpose eq533 eq533
    | exact resolve eq533 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq413 X0
       grind)
    | exact superpose eq413 eq533
    | exact resolve eq533 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0
       have i₂ := eq533 X0 X1
       grind)
    | exact superpose eq533 eq78
    | exact resolve eq78 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq642 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 X0 X2
       have i₂ := eq533 X0 X1
       grind)
    | exact superpose eq533 eq82
    | exact resolve eq82 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq643 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq413 X0
       have i₂ := eq533 X0 X1
       grind)
    | exact superpose eq533 eq413
    | exact resolve eq413 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0
       have i₂ := eq533 X0 X1
       grind)
    | exact superpose eq533 eq426
    | exact resolve eq426 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq731 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq639 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq413 X0
       grind)
    | exact superpose eq413 eq639
    | exact resolve eq639 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq750 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq639 (M.op X0 X0) x
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq639
    | exact resolve eq639 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1139 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq645 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq534 X0 X0
       grind)
    | exact superpose eq534 eq645
    | exact resolve eq645 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq1627 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) (M.op X1 X1)) X1) ∨ (k X2 (σ X0)) = (M.op X2 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq94 X0 X0 X2
       grind)
    | exact superpose eq94 eq9
    | (have j1 := eq94 X0 X0 X2
       grind)
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1705 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) (M.op X1 X1)) X1) ∨ (k X2 (σ X0)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1627 X0 X1 X2
       have j1 := eq12 X2 (σ X0)
       grind)
    | (have r₁ := eq1627 X0 X1 X2
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq1627 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq2255 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq114 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq114
    | exact resolve eq114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2302 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2255 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2255
    | (have j0 := eq2255 X0 X1
       grind)
    | exact resolve eq2255 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2255
  have eq2994 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq623 (M.op (M.op X1 X1) X1) (M.op X0 X1)
       have i₂ := eq623 X1 X0
       grind)
    | exact superpose eq623 eq623
    | exact resolve eq623 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq3093 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1)) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2994 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq2994
    | exact resolve eq2994 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq2994
  have eq3117 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op X1 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3093 X0 X1
       have i₂ := eq415 X1
       grind)
    | exact superpose eq415 eq3093
    | exact resolve eq3093 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093
  have eq3129 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3117 X0 X1
       have i₂ := eq426 X1
       grind)
    | exact superpose eq426 eq3117
    | exact resolve eq3117 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3117
  have eq3330 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq112 x y
       grind)
    | exact superpose eq112 eq16
    | (have j1 := eq112 x y
       grind)
    | exact resolve eq16 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq4563 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1139 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq1139
    | exact resolve eq1139 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq6992 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3330
       have i₂ := eq2302 x y
       grind)
    | exact superpose eq2302 eq3330
    | (have j1 := eq2302 (σ x) (σ y)
       grind)
    | (have r₁ := eq3330
       have r₂ := eq2302 x y
       grind)
    | exact resolve eq3330 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302 eq3330
  have eq6993 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6992
  have eq7149 : (σ x) = (M.op (M.op (σ y) (M.op (M.op (σ y) (σ y)) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq731 (σ y) (σ x)
       have i₂ := eq6993
       grind)
    | exact superpose eq6993 eq731
    | exact resolve eq731 eq6993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6993
  have eq7153 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7149
       have i₂ := eq426 (σ y)
       grind)
    | exact superpose eq426 eq7149
    | exact resolve eq7149 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7149
  have eq7391 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq534 (σ x) (σ y)
       have i₂ := eq7153
       grind)
    | exact superpose eq7153 eq534
    | exact resolve eq534 eq7153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7153
  have eq7404 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7391
       have i₂ := eq426 (σ x)
       grind)
    | exact superpose eq426 eq7391
    | exact resolve eq7391 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7391
  have eq8591 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op (M.op (σ (k (τ X0) (τ X0))) (M.op X2 X2)) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1705 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1705
    | exact resolve eq1705 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705
  have eq8700 : ∀ X0 X1 X2 : G, (M.op (M.op (k (σ (τ X0)) X0) (M.op X2 X2)) X2) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8591 X0 X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq8591
    | (have j0 := eq8591 X0 X1 X2
       grind)
    | exact resolve eq8591 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq8591
  have eq8716 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) (M.op X2 X2)) X2) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8700 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8700
    | (have j0 := eq8700 X0 X1 X2
       grind)
    | exact resolve eq8700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8700
  have eq10460 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq642 X0 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have i₂ := eq620 (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X1 X1) X2
       grind)
    | (have i₁ := eq642 X0 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have i₂ := eq620 (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) X2 (M.op X1 X1)
       grind)
    | exact superpose eq620 eq642
    | exact resolve eq642 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq642
  have eq10706 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 (M.op (M.op X1 X1) X1)))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10460 X0 X1 X2
       have i₂ := eq4563 X1 X1
       grind)
    | exact superpose eq4563 eq10460
    | exact resolve eq10460 eq4563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4563 eq10460
  have eq10783 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10706 X0 X1 X2
       have i₂ := eq426 X1
       grind)
    | exact superpose eq426 eq10706
    | exact resolve eq10706 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq10706
  have eq10803 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10783 X0 X1 X2
       have i₂ := eq3129 X1 X1
       grind)
    | exact superpose eq3129 eq10783
    | exact resolve eq10783 eq3129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129 eq10783
  have eq10811 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10803 X0 X1 X2
       have i₂ := eq415 X1
       grind)
    | exact superpose eq415 eq10803
    | exact resolve eq10803 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq10803
  have eq11674 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X0) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10811 X1 X2 (M.op (M.op X0 X0) X0)
       have i₂ := eq534 X0 X0
       grind)
    | exact superpose eq534 eq10811
    | exact resolve eq10811 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq10811
  have eq47960 : ∀ X0 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq643 (k X0 X0) X2
       have i₂ := eq8716 X0 x X2
       grind)
    | exact superpose eq8716 eq643
    | (have j1 := eq8716 X0 X0 X2
       grind)
    | exact resolve eq643 eq8716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq8716
  have eq48932 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq47960 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47960
  have eq48933 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48932 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48932
  have eq49575 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq48933 (σ X0)
       grind)
    | exact superpose eq48933 eq15
    | exact resolve eq15 eq48933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49583 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq48933 (τ X0)
       grind)
    | exact superpose eq48933 eq32
    | exact resolve eq32 eq48933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq49627 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49583 X0
       have i₂ := eq48933 X0
       grind)
    | exact superpose eq48933 eq49583
    | exact resolve eq49583 eq48933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49583
  have eq49632 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49575 X0
       have i₂ := eq48933 X0
       grind)
    | exact superpose eq48933 eq49575
    | exact resolve eq49575 eq48933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48933 eq49575
  have eq50655 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq750 (τ X0)
       have i₂ := eq49627 X0
       grind)
    | exact superpose eq49627 eq750
    | exact resolve eq750 eq49627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq49627
  have eq52845 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50655 (σ x)
       have i₂ := eq7404
       grind)
    | exact superpose eq7404 eq50655
    | exact resolve eq50655 eq7404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7404 eq50655
  have eq52919 : y = (M.op (τ (σ x)) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52845
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq52845
    | exact resolve eq52845 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52845
  have eq52961 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52919
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52919
    | exact resolve eq52919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52919
  have eq52962 : y = (M.op x y) := by grind
  clear eq52961
  have eq53712 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) (M.op (M.op X0 X0) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq11674 X0 x y
       have i₂ := eq52962
       grind)
    | exact superpose eq52962 eq11674
    | exact resolve eq11674 eq52962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11674
  have eq53718 : y = (M.op x x) := by
    first
    | (have i₁ := eq53712 x
       have i₂ := eq731 x y
       grind)
    | exact superpose eq731 eq53712
    | exact resolve eq53712 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq53712
  have eq54539 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) y) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq53718
       grind)
    | exact superpose eq53718 eq9
    | exact resolve eq9 eq53718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54586 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq639 X0 x
       have i₂ := eq53718
       grind)
    | exact superpose eq53718 eq639
    | exact resolve eq639 eq53718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq63669 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) y) x) := by
    intro X0
    first
    | (have i₁ := eq54539 (σ X0)
       have i₂ := eq49632 X0
       grind)
    | exact superpose eq49632 eq54539
    | exact resolve eq54539 eq49632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49632 eq54539
  have eq93053 : (σ x) = (M.op (M.op (σ y) y) x) := by
    first
    | (have i₁ := eq63669 x
       have i₂ := eq53718
       grind)
    | exact superpose eq53718 eq63669
    | exact resolve eq63669 eq53718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53718 eq63669
  have eq94411 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54586 (σ y)
       have i₂ := eq93053
       grind)
    | exact superpose eq93053 eq54586
    | exact resolve eq54586 eq93053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54586 eq93053
  have eq95962 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94411
       grind)
    | exact superpose eq94411 eq16
    | exact resolve eq16 eq94411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94411
  have eq96005 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq95962
       have i₂ := eq52962
       grind)
    | exact superpose eq52962 eq95962
    | exact resolve eq95962 eq52962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52962 eq95962
  have eq96006 : False := by grind
  exact eq96006

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_x_pxy_Equation2653 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq105 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq105
    | exact resolve eq105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq9
    | exact resolve eq9 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0)
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq9
    | exact resolve eq9 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq9
    | exact resolve eq9 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq106
    | exact resolve eq106 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq115 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq113
    | exact resolve eq113 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq113
  have eq442 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq111 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq110 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq110 eq111
    | exact resolve eq111 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq447 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq442 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq442
    | exact resolve eq442 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq442
  have eq472 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq447 X0
       grind)
    | exact superpose eq447 eq9
    | exact resolve eq9 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0
       have i₂ := eq472 X0 X1
       grind)
    | exact superpose eq472 eq447
    | exact resolve eq447 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq472
  have eq637 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq646 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq637
    | (have j0 := eq637 X0 X1
       grind)
    | exact resolve eq637 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq665 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (M.op (σ X1) (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq646 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq646
    | (have j0 := eq646 (σ X0) (σ X1)
       grind)
    | exact resolve eq646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq702 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq665
    | (have j0 := eq665 X0 X1
       grind)
    | exact resolve eq665 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq21458 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X1) X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq527 (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) X0
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq527
    | exact resolve eq527 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq52294 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq21458 X1 X0
       grind)
    | exact superpose eq21458 eq110
    | exact resolve eq110 eq21458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq21458
  have eq53052 : ∀ X0 X1 : G, (σ (σ X1)) = (M.op (M.op (σ (σ (M.op X0 X0))) (σ (σ (M.op X0 X0)))) (M.op (σ (σ X0)) (σ (σ X0)))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52294 (σ (σ X1)) (σ (σ X0))
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq52294
    | (have j1 := eq702 X1 X0
       grind)
    | exact resolve eq52294 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq53345 : ∀ X0 X1 : G, (σ (σ X1)) = (M.op (M.op (σ (σ (M.op X0 X0))) (σ (σ (M.op X0 X0)))) (σ (M.op (σ X0) (σ X0)))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53052 X0 X1
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq53052
    | (have j0 := eq53052 X0 X1
       grind)
    | exact resolve eq53052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53052
  have eq53507 : ∀ X0 X1 : G, (σ (σ X1)) = (M.op (M.op (σ (σ (M.op X0 X0))) (σ (σ (M.op X0 X0)))) (σ (σ (M.op X0 X0)))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53345 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq53345
    | (have j0 := eq53345 X0 X1
       grind)
    | exact resolve eq53345 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53345
  have eq53592 : ∀ X0 X1 : G, (σ (σ X1)) = (M.op (σ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) (σ (σ (M.op X0 X0)))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53507 X0 X1
       have i₂ := eq22 (σ (M.op X0 X0))
       grind)
    | exact superpose eq22 eq53507
    | (have j0 := eq53507 X0 X1
       grind)
    | exact resolve eq53507 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53507
  have eq53619 : ∀ X0 X1 : G, (σ (σ X1)) = (σ (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ (M.op X0 X0)))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53592 X0 X1
       have i₂ := eq115 (σ (M.op X0 X0))
       grind)
    | exact superpose eq115 eq53592
    | (have j0 := eq53592 X0 X1
       grind)
    | exact resolve eq53592 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53592
  have eq53635 : ∀ X0 X1 : G, (σ (σ X1)) = (σ (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ (M.op X0 X0)))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53619 X0 X1
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq53619
    | (have j0 := eq53619 X0 X1
       grind)
    | exact resolve eq53619 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53619
  have eq53642 : ∀ X0 X1 : G, (σ (σ X1)) = (σ (σ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53635 X0 X1
       have i₂ := eq115 (M.op X0 X0)
       grind)
    | exact superpose eq115 eq53635
    | (have j0 := eq53635 X0 X1
       grind)
    | exact resolve eq53635 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq53635
  have eq53644 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53642 X0 X1
       have i₂ := eq52294 X0 X0
       grind)
    | exact superpose eq52294 eq53642
    | (have j0 := eq53642 X0 X1
       grind)
    | exact resolve eq53642 eq52294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52294 eq53642
  have eq53645 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq53644 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53644
  have eq258367 : ∀ X0 X1 : G, (σ (σ (k X1 (τ X0)))) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53645 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53645
    | exact resolve eq53645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53645
  have eq258591 : ∀ X0 X1 : G, (σ (k (σ X1) X0)) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq258367 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq258367
    | (have j0 := eq258367 X0 X1
       grind)
    | exact resolve eq258367 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq258367
  have eq258932 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq258591 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq258591
    | exact resolve eq258591 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258591
  have eq259244 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq258932 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq258932
    | (have j0 := eq258932 (τ X0) (τ X1)
       grind)
    | exact resolve eq258932 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq259518 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259244 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq259244
    | (have j0 := eq259244 X0 X1
       grind)
    | exact resolve eq259244 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259244
  have eq259537 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259518 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq259518
    | (have j0 := eq259518 X0 X1
       grind)
    | exact resolve eq259518 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259518
  have eq259542 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259537 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq259537
    | (have j0 := eq259537 X0 X1
       grind)
    | exact resolve eq259537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259537
  have eq259547 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq259542 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq259542
    | (have j0 := eq259542 X0 X1
       grind)
    | exact resolve eq259542 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259542
  have eq259552 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq259547 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq259547
    | (have j0 := eq259547 X0 X1
       grind)
    | exact resolve eq259547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259547
  have eq259569 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq258932 X0 X1
       have i₂ := eq259552 X0 X1
       grind)
    | exact superpose eq259552 eq258932
    | (have j0 := eq258932 X0 X1
       have j1 := eq259552 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq258932 eq259552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258932 eq259552
  have eq285539 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq259569 x y
       grind)
    | exact superpose eq259569 eq16
    | (have j1 := eq259569 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq259569 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq259569 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq259569 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq259569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259569
  have eq285665 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq285539
  have eq285933 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq285665
       grind)
    | exact superpose eq285665 eq10
    | exact resolve eq10 eq285665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285665
  have eq286288 : x = y ∨ x = y := by
    first
    | (have i₁ := eq285933
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq285933
    | exact resolve eq285933 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285933
  have eq286289 : x = y := by grind
  clear eq286288
  have eq286314 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq286289
       grind)
    | exact superpose eq286289 eq16
    | exact resolve eq16 eq286289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286289
  have eq286315 : False := by grind
  exact eq286315

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pxy_pyx_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq214 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq221 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq214 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq222 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq221 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq228 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq222 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq222 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq222 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq239 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq228 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq228
    | (have j0 := eq228 X0 X1
       grind)
    | exact resolve eq228 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq240 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq239 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq245 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq240 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq240
    | exact resolve eq240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq240 x y
       grind)
    | exact superpose eq240 eq16
    | exact resolve eq16 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq324 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq245 X0 (τ X1)
       grind)
    | exact superpose eq245 eq18
    | exact resolve eq18 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq245
  have eq337 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq324
    | exact resolve eq324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq343 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq337
    | exact resolve eq337 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq359 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq256
       have i₂ := eq343 x y
       grind)
    | exact superpose eq343 eq256
    | exact resolve eq256 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq343
  have eq360 : False := by grind
  exact eq360

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyy_pxy_pyy_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq46
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq49 X1 X1
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq49 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq49
  have eq154 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq159 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq154 X0 X1
       have j1 := eq51 X0 X1
       grind)
    | (have r₁ := eq154 X0 X1
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq154 X0 X0
       have r₂ := eq51 X0 X0
       grind)
    | exact resolve eq154 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq154
  have eq295 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq159 (σ X0) (σ X1)
       grind)
    | exact superpose eq159 eq15
    | exact resolve eq15 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq295
    | exact resolve eq295 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq295
  have eq302 : False := by grind
  exact eq302

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq529 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12739 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq529 X0 X1
       grind)
    | exact superpose eq529 eq12
    | (have j0 := eq12 (τ X0) X1
       have j1 := eq529 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq529 X0 X1
       grind)
    | exact resolve eq12 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq12769 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq12739 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12739
  have eq17782 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq12769 X0 X1
       grind)
    | exact superpose eq12769 eq10
    | (have j1 := eq12769 X0 X1
       grind)
    | exact resolve eq10 eq12769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12769
  have eq17882 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17782 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq17782
    | (have j0 := eq17782 X0 X1
       grind)
    | exact resolve eq17782 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17782
  have eq17883 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq17882 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17882
  have eq17947 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17883 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17883
    | exact resolve eq17883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17985 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq17883 X0 X1
       grind)
    | exact superpose eq17883 eq17
    | (have j1 := eq17883 X0 X1
       grind)
    | exact resolve eq17 eq17883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq17883
  have eq18234 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq17947 (σ X0) (σ X1)
       grind)
    | exact superpose eq17947 eq15
    | (have j1 := eq17947 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq17947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17947
  have eq18332 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17985 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17985
    | exact resolve eq17985 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17985
  have eq18498 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18332 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18332
    | (have j0 := eq18332 X0 X1
       grind)
    | exact resolve eq18332 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18332
  have eq24228 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18234 x y
       grind)
    | exact superpose eq18234 eq16
    | (have j1 := eq18234 x y
       grind)
    | exact resolve eq16 eq18234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18234
  have eq24341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq24228
       have i₂ := eq18498 x y
       grind)
    | exact superpose eq18498 eq24228
    | (have j1 := eq18498 (σ x) (σ y)
       grind)
    | (have r₁ := eq24228
       have r₂ := eq18498 x y
       grind)
    | exact resolve eq24228 eq18498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24344 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq24341
  have eq24355 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq24344
       grind)
    | exact superpose eq24344 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq24344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24357 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq24344
       grind)
    | exact superpose eq24344 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq24344
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq24344
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq24344
       grind)
    | exact resolve eq13 eq24344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24344
  have eq24361 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq24357
  have eq24363 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq24355
       have r₂ := eq24361
       grind)
    | exact resolve eq24355 eq24361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24355 eq24361
  have eq24370 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq24228
       have i₂ := eq24363
       grind)
    | exact superpose eq24363 eq24228
    | exact resolve eq24228 eq24363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24228 eq24363
  have eq24374 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq24370
  have eq24375 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq24374
  have eq24390 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq24375
       grind)
    | exact superpose eq24375 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq24375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24392 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq24375
       grind)
    | exact superpose eq24375 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq24375
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq24375
       grind)
    | exact resolve eq13 eq24375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24375
  have eq24396 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq24392
  have eq24401 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24396
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq24396
    | exact resolve eq24396 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24396
  have eq24403 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24390
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq24390
    | exact resolve eq24390 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24390
  have eq24414 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq24403
       have r₂ := eq24401
       grind)
    | exact resolve eq24403 eq24401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24401 eq24403
  have eq24427 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24414
       grind)
    | exact superpose eq24414 eq16
    | exact resolve eq16 eq24414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24414
  have eq24498 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq24427
       have i₂ := eq18498 x y
       grind)
    | exact superpose eq18498 eq24427
    | (have j1 := eq18498 x y
       grind)
    | (have r₁ := eq24427
       have r₂ := eq18498 x y
       grind)
    | exact resolve eq24427 eq18498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18498
  have eq24501 : (M.op x y) = (M.op y x) := by grind
  clear eq24498
  have eq24513 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq24501
       grind)
    | exact superpose eq24501 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq24501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24515 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq24501
       grind)
    | exact superpose eq24501 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq24501
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq24501
       grind)
    | exact resolve eq13 eq24501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24501
  have eq24519 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq24515
  have eq24521 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq24513
       have r₂ := eq24519
       grind)
    | exact resolve eq24513 eq24519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24513 eq24519
  have eq24528 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq24427
       have i₂ := eq24521
       grind)
    | exact superpose eq24521 eq24427
    | exact resolve eq24427 eq24521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24427 eq24521
  have eq24533 : False := by grind
  exact eq24533
