import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
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
  clear eq25 eq36
  have eq47 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq14 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq67 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq64
    | exact resolve eq64 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq67
    | exact resolve eq67 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
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
  have eq348 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq80 x
       grind)
    | exact superpose eq80 eq44
    | (have j1 := eq80 x
       grind)
    | exact resolve eq44 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq80
  have eq441 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq47 X1 X0 X3
       grind)
    | exact superpose eq47 eq47
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (σ y) X0 (σ x)
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq4646 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq170 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq170
    | (have j0 := eq170 x
       grind)
    | exact resolve eq170 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq4665 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq4646
    | exact resolve eq4646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646
  have eq4681 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4665
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq4665
    | exact resolve eq4665 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4665
  have eq4686 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq4681
    | exact resolve eq4681 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4681
  have eq5394 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq441 x X2 X0 X1
       grind)
    | exact superpose eq441 eq14
    | exact resolve eq14 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq11161 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq27 eq5394
    | (have j0 := eq5394 X0 (σ x) (σ y)
       grind)
    | exact resolve eq5394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11165 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5394 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq5394 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq5394 eq5394
    | exact resolve eq5394 eq5394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5394
  have eq11213 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq11161 eq14
    | exact resolve eq14 eq11161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11161
  have eq14157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq69 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14157
    | exact resolve eq14157 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14157
  have eq14169 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq14158
       have r₂ := eq28
       grind)
    | exact resolve eq14158 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14158
  have eq14171 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14169
    | exact resolve eq14169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14169
  have eq14174 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14171 eq78
    | (have r₁ := eq78
       have r₂ := eq14171
       grind)
    | exact resolve eq78 eq14171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14171
  have eq14190 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq14174
  have eq14191 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq14190
  have eq14446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14191 eq69
    | exact resolve eq69 eq14191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14191
  have eq14455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq14446
  have eq14458 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq14455
       have r₂ := eq28
       grind)
    | exact resolve eq14455 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14455
  have eq14713 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  have eq14720 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq14458 eq11165
    | exact resolve eq11165 eq14458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14458
  have eq14726 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq14720
    | exact resolve eq14720 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14720
  have eq14729 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq348
       have i₂ := eq14726
       grind)
    | exact superpose eq14726 eq348
    | exact resolve eq348 eq14726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14730 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq14726
       grind)
    | exact superpose eq14726 eq77
    | (have r₁ := eq77
       have r₂ := eq14726
       grind)
    | exact resolve eq77 eq14726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14726
  have eq14746 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14730
  have eq14747 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14746
  have eq14748 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq14729
    | exact resolve eq14729 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14729
  have eq15020 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq14747
       grind)
    | exact superpose eq14747 eq45
    | exact resolve eq45 eq14747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14747
  have eq15040 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq15020
    | exact resolve eq15020 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15020
  have eq15073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15040 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq15040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15073
    | exact resolve eq15073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15073
  have eq15087 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15076
       have r₂ := eq28
       grind)
    | exact resolve eq15076 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15076
  have eq15089 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15087
    | exact resolve eq15087 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15087
  have eq15098 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq14713 eq69
    | exact resolve eq69 eq14713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq14713
  have eq15110 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by grind
  clear eq15098
  have eq15123 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq348
       have i₂ := eq15110
       grind)
    | exact superpose eq15110 eq348
    | exact resolve eq348 eq15110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq15124 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq15110
       grind)
    | exact superpose eq15110 eq77
    | (have r₁ := eq77
       have r₂ := eq15110
       grind)
    | exact resolve eq77 eq15110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq15110
  have eq15140 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq15124
  have eq15141 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq15140
  have eq15142 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq15123
    | exact resolve eq15123 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15123
  have eq15673 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq15141
       grind)
    | exact superpose eq15141 eq45
    | exact resolve eq45 eq15141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15141
  have eq15693 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq15673
    | exact resolve eq15673 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15673
  have eq15728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15693 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq15693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq15728
    | exact resolve eq15728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15728
  have eq15744 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq15733
       have r₂ := eq28
       grind)
    | exact resolve eq15733 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15733
  have eq15746 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq15744
    | exact resolve eq15744 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15744
  have eq22176 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15089 eq78
    | (have r₁ := eq78
       have r₂ := eq15089
       grind)
    | exact resolve eq78 eq15089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22190 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15089 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15089
       grind)
    | exact resolve eq12 eq15089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15089
  have eq22191 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq22190
  have eq22192 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq22191
  have eq22193 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22176
  have eq22194 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22193
  have eq23234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22192 eq14748
    | exact resolve eq14748 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14748 eq22192
  have eq23243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq23234
  have eq23249 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23243
       have r₂ := eq28
       grind)
    | exact resolve eq23243 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23243
  have eq23266 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23249 eq11165
    | exact resolve eq11165 eq23249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23249
  have eq23272 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq23266
    | exact resolve eq23266 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23266
  have eq23273 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23272
  have eq23543 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11165 y y
       have i₂ := eq23273
       grind)
    | exact superpose eq23273 eq11165
    | exact resolve eq11165 eq23273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23273
  have eq23549 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23543
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23543
    | exact resolve eq23543 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23543
  have eq23550 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23549
  have eq23554 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23550 eq28
    | exact resolve eq28 eq23550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23550
  have eq26316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22194 eq15040
    | exact resolve eq15040 eq22194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15040 eq22194
  have eq26337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq26316
  have eq26356 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26337
       have r₂ := eq28
       grind)
    | exact resolve eq26337 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26337
  have eq26629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26356 eq11165
    | exact resolve eq11165 eq26356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26356
  have eq26635 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq26629
    | exact resolve eq26629 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26629
  have eq26636 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26635
  have eq26646 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26636
  have eq26920 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq26646
       grind)
    | exact superpose eq26646 eq45
    | exact resolve eq45 eq26646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq26646
  have eq26961 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26920
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26920
    | exact resolve eq26920 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26920
  have eq26981 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26961 eq4686
    | exact resolve eq4686 eq26961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4686
  have eq27011 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq26981
  have eq29740 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27011 eq78
    | (have r₁ := eq78
       have r₂ := eq27011
       grind)
    | exact resolve eq78 eq27011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq27011
  have eq29765 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29740
  have eq29766 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29765
  have eq30642 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29766 eq26961
    | exact resolve eq26961 eq29766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26961 eq29766
  have eq30645 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30642
  have eq30679 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30645 eq11165
    | exact resolve eq11165 eq30645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30645
  have eq30685 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq30679
    | exact resolve eq30679 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30679
  have eq30686 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30685
  have eq30952 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq30686 eq28
    | exact resolve eq28 eq30686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq30953 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq30686 eq443
    | exact resolve eq443 eq30686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq30957 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq30686 eq11213
    | exact resolve eq11213 eq30686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11213
  have eq31521 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq15746 eq30957
    | exact resolve eq30957 eq15746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15746 eq30957
  have eq31551 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq31521 X0
       grind)
    | (have r₁ := eq31521 X0
       have r₂ := eq30952
       grind)
    | exact resolve eq31521 eq30952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31521
  have eq31552 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30686 eq31551
    | exact resolve eq31551 eq30686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30686 eq31551
  have eq37000 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31552 eq30953
    | exact resolve eq30953 eq31552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30953 eq31552
  have eq37294 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq37000
  have eq37610 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq37294 eq15693
    | exact resolve eq15693 eq37294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15693 eq37294
  have eq37621 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq37610
  have eq37647 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq37621
       have r₂ := eq30952
       grind)
    | exact resolve eq37621 eq30952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37621
  have eq37688 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq37647
  have eq37991 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq37688 eq15142
    | exact resolve eq15142 eq37688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15142 eq37688
  have eq38004 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq37991
  have eq38013 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq38004
       have r₂ := eq23554
       grind)
    | exact resolve eq38004 eq23554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23554 eq38004
  have eq38038 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11165 y y
       have i₂ := eq38013
       grind)
    | exact superpose eq38013 eq11165
    | exact resolve eq11165 eq38013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11165 eq38013
  have eq38044 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38038
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq38038
    | exact resolve eq38038 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq38038
  have eq38045 : x = (M.op x y) := by grind
  clear eq38044
  have eq38311 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq38045 eq21
    | exact resolve eq21 eq38045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq38045
  have eq38562 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq38311
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38311
    | exact resolve eq38311 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq38311
  have eq38563 : False := by grind
  exact eq38563

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq42 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq27
  have eq46 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq42
    | exact resolve eq42 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq42
  have eq75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq75 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq75 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq75 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq119 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq120 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq120
    | (have j0 := eq120 X0 X1
       grind)
    | exact resolve eq120 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq116 X1 X0
       grind)
    | (have r₁ := eq122 X1 X0
       have r₂ := eq116 X0 X1
       grind)
    | (have r₁ := eq122 X1 (k X0 X1)
       have r₂ := eq116 X0 X1
       grind)
    | (have r₁ := eq122 X1 X1
       have r₂ := eq116 X1 X1
       grind)
    | exact resolve eq122 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq122
  have eq475 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq125 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq125
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq125 y x
       grind)
    | exact superpose eq125 eq16
    | (have j1 := eq125 y x
       grind)
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq498 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq475 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq475
    | (have j0 := eq475 X0 X1
       grind)
    | exact resolve eq475 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq475
  have eq716 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq96 x X2 X0 X1
       grind)
    | exact superpose eq96 eq9
    | exact resolve eq9 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq739 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq716 x X1 X0
       grind)
    | exact superpose eq716 eq9
    | exact resolve eq9 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq786 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq498
    | exact resolve eq498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq899 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq786 (τ X0) X1
       grind)
    | exact superpose eq786 eq18
    | (have j1 := eq786 (τ X0) X1
       grind)
    | exact resolve eq18 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1106 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq899 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq899
    | exact resolve eq899 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq1169 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1106 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1106
    | (have j0 := eq1106 X0 X1
       grind)
    | exact resolve eq1106 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq2105 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq482
       have i₂ := eq1169 x y
       grind)
    | exact superpose eq1169 eq482
    | (have j1 := eq1169 (σ x) (σ y)
       grind)
    | (have r₁ := eq482
       have r₂ := eq1169 x y
       grind)
    | exact resolve eq482 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq2106 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2105
  have eq2112 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2106
  have eq2285 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq482
       have i₂ := eq2112
       grind)
    | exact superpose eq2112 eq482
    | exact resolve eq482 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq2112
  have eq2286 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2285
  have eq2287 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2286
  have eq2305 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq46 y
       have i₂ := eq2287
       grind)
    | exact superpose eq2287 eq46
    | exact resolve eq46 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq2318 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq739 (σ y) (σ y)
       have i₂ := eq2287
       grind)
    | exact superpose eq2287 eq739
    | exact resolve eq739 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2287
  have eq2331 : x = (k x y) := by
    first
    | (have i₁ := eq2305
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2305
    | exact resolve eq2305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305
  have eq2389 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq786 x y
       have i₂ := eq2331
       grind)
    | exact superpose eq2331 eq786
    | (have j0 := eq786 x y
       grind)
    | exact resolve eq786 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq2331
  have eq2598 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq16
    | exact resolve eq16 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318
  have eq2714 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2598
       have i₂ := eq2389
       grind)
    | exact superpose eq2389 eq2598
    | exact resolve eq2598 eq2389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq2719 : x = (M.op y y) := by grind
  clear eq2714
  have eq2783 : x = (M.op x y) := by
    first
    | (have i₁ := eq739 y y
       have i₂ := eq2719
       grind)
    | exact superpose eq2719 eq739
    | exact resolve eq739 eq2719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq2719
  have eq2790 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2598
       have i₂ := eq2783
       grind)
    | exact superpose eq2783 eq2598
    | exact resolve eq2598 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598 eq2783
  have eq2795 : False := by grind
  exact eq2795

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq27
    | exact resolve eq27 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq48 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq51 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq34
    | exact resolve eq34 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq85 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq114 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq9
    | (have j1 := eq76 X0 X0
       grind)
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq125 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq118 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq158 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k X2 (τ X3)))) = (k (k (σ X0) X1) (k (σ X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32 X2 X3 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq32
    | exact resolve eq32 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq191 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  clear eq49
  have eq197 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq191
    | (have j0 := eq191 X0 X1 X2
       grind)
    | exact resolve eq191 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq198 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq197 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq201 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq198
    | exact resolve eq198 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X1 (M.op X2 (k (σ (τ X0)) X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125 (τ X0) X1 X2
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq125
    | (have j0 := eq125 (τ X0) X1 X2
       grind)
    | exact resolve eq125 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq645 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (k X0 X0)))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq618 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq618
    | (have j0 := eq618 X0 X1 X2
       grind)
    | exact resolve eq618 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq651 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (k X0 X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq645 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq645
    | (have j0 := eq645 X0 X1 X2
       grind)
    | exact resolve eq645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq919 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq198 (k X0 X0) X0 x
       have i₂ := eq651 X0 x (k X0 X0)
       grind)
    | exact superpose eq651 eq198
    | (have j1 := eq651 X0 x x
       grind)
    | exact resolve eq198 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq1018 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (M.op (τ X0) X1) X2
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq34
    | (have j1 := eq78 X0 X1
       grind)
    | exact resolve eq34 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1033 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1018 X0 X1 X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | exact superpose eq51 eq1018
    | (have j0 := eq1018 X0 X1 X2
       grind)
    | exact resolve eq1018 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1018
  have eq1144 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq121 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq121
    | (have j0 := eq121 (τ X0) (τ X1)
       grind)
    | exact resolve eq121 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1164 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1144 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1144
    | (have j0 := eq1144 X0 X1
       grind)
    | exact resolve eq1144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1170 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1164 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1164
    | (have j0 := eq1164 X0 X1
       grind)
    | exact resolve eq1164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1172 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1170 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1170
    | (have j0 := eq1170 X0 X1
       grind)
    | exact resolve eq1170 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1173 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1172 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1172
    | (have j0 := eq1172 X0 X1
       grind)
    | exact resolve eq1172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1174 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1173 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1173
    | (have j0 := eq1173 X0 X1
       grind)
    | exact resolve eq1173 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1175 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1174 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1174
    | (have j0 := eq1174 X0 X1
       grind)
    | exact resolve eq1174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1262 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq85 x X2 X0 X1
       grind)
    | exact superpose eq85 eq198
    | exact resolve eq198 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq1264 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq85 x X2 X0 X1
       grind)
    | exact superpose eq85 eq9
    | exact resolve eq9 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1350 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1264 x X1 X0
       grind)
    | exact superpose eq1264 eq9
    | exact resolve eq9 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1351 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq1264 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1264 eq9
    | exact resolve eq9 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1358 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1262 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq1264 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1264 eq1262
    | exact resolve eq1262 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1366 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq114
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq114 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1367 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq1366
  have eq1437 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (M.op X0 (σ X1)) X1
       have i₂ := eq1358 (σ X1) X0
       grind)
    | exact superpose eq1358 eq27
    | exact resolve eq27 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1438 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (M.op X0 (τ X1))
       have i₂ := eq1358 (τ X1) X0
       grind)
    | exact superpose eq1358 eq19
    | exact resolve eq19 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq6306 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1264 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1351 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1351 eq1264
    | exact resolve eq1264 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq1351
  have eq6394 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq201 (M.op X0 (M.op X1 X2)) X2 X2
       have i₂ := eq6306 X0 X1 X2
       grind)
    | exact superpose eq6306 eq201
    | exact resolve eq201 eq6306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq6306
  have eq6961 : ∀ X0 X1 X2 X3 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (M.op X3 (σ X0)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34 X0 (M.op X1 (M.op X2 (M.op X3 (σ X0))))
       have i₂ := eq6394 (σ X0) X2 X3 X1
       grind)
    | exact superpose eq6394 eq34
    | exact resolve eq34 eq6394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq6394
  have eq6986 : ∀ X0 X1 X2 X3 : G, (k X0 (τ (M.op X1 (M.op X2 (M.op X3 (σ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6961 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6961
    | exact resolve eq6961 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6961
  have eq7505 : ∀ X0 X1 X2 X3 X4 : G, (τ (k X1 (σ X0))) = (k (τ X1) (k X0 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X0))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq40 X0 (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X0)))))) X1
       have i₂ := eq6986 (σ X0) X2 X3 X4
       grind)
    | exact superpose eq6986 eq40
    | exact resolve eq40 eq6986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq7534 : ∀ X0 X1 X2 X3 X4 : G, (k (τ X1) X0) = (k (τ X1) (k X0 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X0))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7505 X0 X1 X2 X3 X4
       have i₂ := eq27 X1 X0
       grind)
    | exact superpose eq27 eq7505
    | exact resolve eq7505 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7505
  have eq24804 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq919 (τ X0)
       have i₂ := eq1033 X0 (τ X0) X0
       grind)
    | exact superpose eq1033 eq919
    | (have j0 := eq919 (τ X0)
       have j1 := eq1033 X0 (τ X0) x
       grind)
    | exact resolve eq919 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919 eq1033
  have eq24875 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq24804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24804
  have eq24935 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq24875 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq24875
    | (have j0 := eq24875 X0
       grind)
    | exact resolve eq24875 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24875
  have eq24994 : ∀ X0 : G, (M.op (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq24935
  have eq25026 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24994 X0
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq24994
    | (have j0 := eq24994 X0
       grind)
    | exact resolve eq24994 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq24994
  have eq25102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq25026
  have eq25160 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25102 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq25102
    | (have j0 := eq25102 X0
       grind)
    | exact resolve eq25102 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq25102
  have eq25161 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq25160 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25160
  have eq25204 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq25161 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25161
    | exact resolve eq25161 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25161
  have eq25363 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq25204 X0
       have i₂ := eq27 (σ X0) X0
       grind)
    | exact superpose eq27 eq25204
    | exact resolve eq25204 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25204
  have eq25385 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq25363 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25363
    | exact resolve eq25363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25363
  have eq25689 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq25385 (σ X0)
       grind)
    | exact superpose eq25385 eq15
    | exact resolve eq15 eq25385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25714 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (k (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 X1 X0 X1
       have i₂ := eq25385 (k X0 (τ X1))
       grind)
    | exact superpose eq25385 eq158
    | exact resolve eq158 eq25385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq25731 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25714 X0 X1
       have i₂ := eq25385 (k (σ X0) X1)
       grind)
    | exact superpose eq25385 eq25714
    | exact resolve eq25714 eq25385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25714
  have eq25754 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25689 X0
       have i₂ := eq25385 X0
       grind)
    | exact superpose eq25385 eq25689
    | exact resolve eq25689 eq25385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25385 eq25689
  have eq26751 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1350 (σ X0) (σ X0)
       have i₂ := eq25754 X0
       grind)
    | exact superpose eq25754 eq1350
    | exact resolve eq1350 eq25754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266966 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X0)) ≠ (σ (k (τ X0) X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))))) ∨ (σ (τ X0)) = (M.op (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))))) (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq121 (τ X0) (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))))
       have i₂ := eq7534 X1 X0 X2 X3 X4
       grind)
    | exact superpose eq7534 eq121
    | (have j0 := eq121 (τ X0) (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))))
       grind)
    | exact resolve eq121 eq7534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq7534
  have eq266977 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X0)) ≠ (k X0 (σ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))))) ∨ (σ (τ X0)) = (M.op (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))))) (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq266966 X0 X1 X2 X3 X4
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq266966
    | (have j0 := eq266966 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq266966 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq266966
  have eq267162 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (σ X1)) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))))) ∨ (σ (τ X0)) = (M.op (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))))) (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq266977 X0 X1 X2 X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq266977
    | (have j0 := eq266977 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq266977 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266977
  have eq267320 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ X1) (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))) ∨ (k X0 (σ X1)) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))))) (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq267162 X0 X1 X2 X3 X4
       have i₂ := eq19 (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))) X1
       grind)
    | exact superpose eq19 eq267162
    | (have j0 := eq267162 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq267162 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq267162
  have eq267409 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ X1)) ∨ (k X0 (σ X1)) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))))) (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq267320 X0 X1 X2 X3 X4
       have i₂ := eq6986 (σ X1) X2 X3 X4
       grind)
    | exact superpose eq6986 eq267320
    | (have j0 := eq267320 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq267320 eq6986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267320
  have eq267452 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))))) (σ (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq267409 X0 X1 X2 X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq267409
    | (have j0 := eq267409 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq267409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267409
  have eq267473 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X0)) = (σ (M.op (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))) (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))))) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) ≠ X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq267452 X0 X1 X2 X3 X4
       have i₂ := eq25754 (k X1 (τ (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))))
       grind)
    | exact superpose eq25754 eq267452
    | (have j0 := eq267452 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq267452 eq25754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267452
  have eq267485 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X0)) = (M.op (k (σ X1) (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))) (k (σ X1) (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1)))))))) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) ≠ X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq267473 X0 X1 X2 X3 X4
       have i₂ := eq25731 X1 (τ (M.op X2 (M.op X3 (M.op X4 (σ (σ X1))))))
       grind)
    | exact superpose eq25731 eq267473
    | (have j0 := eq267473 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq267473 eq25731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25731 eq267473
  have eq267491 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq267485 X0 X1 X1 x x
       have i₂ := eq6986 (σ X1) X1 x x
       grind)
    | exact superpose eq6986 eq267485
    | (have j0 := eq267485 X0 X1 x x x
       grind)
    | exact resolve eq267485 eq6986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6986 eq267485
  have eq267496 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq267491 X0 X1
       have i₂ := eq25754 X1
       grind)
    | exact superpose eq25754 eq267491
    | (have j0 := eq267491 X0 X1
       grind)
    | exact resolve eq267491 eq25754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267491
  have eq267501 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ X0 ∨ (M.op X0 (σ X1)) = X0 ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq267496 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq267496
    | (have j0 := eq267496 X0 X1
       grind)
    | exact resolve eq267496 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267496
  have eq267633 : ∀ X0 X1 : G, (σ (M.op X0 (τ (σ X1)))) ≠ (σ (M.op X0 (τ (σ X1)))) ∨ (σ (M.op X0 (τ (σ X1)))) = (M.op (σ (M.op X0 (τ (σ X1)))) (σ X1)) ∨ (σ (M.op X0 (τ (σ X1)))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267501 (σ (M.op X0 (τ (σ X1)))) X1
       have i₂ := eq1438 X0 (σ X1)
       grind)
    | exact superpose eq1438 eq267501
    | (have j0 := eq267501 (σ (M.op X0 (τ (σ X1)))) X1
       grind)
    | (have r₁ := eq267501 (σ (M.op X0 (τ (σ X1)))) X1
       have r₂ := eq1438 X0 (σ X1)
       grind)
    | exact resolve eq267501 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438 eq267501
  have eq267707 : ∀ X0 X1 : G, (σ (M.op X0 (τ (σ X1)))) = (M.op (σ (M.op X0 (τ (σ X1)))) (σ X1)) ∨ (σ (M.op X0 (τ (σ X1)))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq267633 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267633
  have eq267768 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (σ (M.op X0 (τ (σ X1)))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267707 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq267707
    | (have j0 := eq267707 X0 X1
       grind)
    | exact resolve eq267707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267707
  have eq267863 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (σ (M.op X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267768 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq267768
    | (have j0 := eq267768 X0 X1
       grind)
    | exact resolve eq267768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267768
  have eq307724 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq267863 x y
       have i₂ := eq1367
       grind)
    | exact superpose eq1367 eq267863
    | exact resolve eq267863 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367 eq267863
  have eq307946 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq307724
  have eq308073 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq307946
       have i₂ := eq25754 y
       grind)
    | exact superpose eq25754 eq307946
    | exact resolve eq307946 eq25754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25754 eq307946
  have eq308074 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq308073
  have eq310613 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq308074
       grind)
    | exact superpose eq308074 eq16
    | exact resolve eq16 eq308074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310618 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1437 (σ x) y
       have i₂ := eq308074
       grind)
    | exact superpose eq308074 eq1437
    | exact resolve eq1437 eq308074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437 eq308074
  have eq310725 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq310618
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq310618
    | exact resolve eq310618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310618
  have eq310753 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1175 x y
       have i₂ := eq310725
       grind)
    | exact superpose eq310725 eq1175
    | (have j0 := eq1175 x y
       grind)
    | (have r₁ := eq1175 x y
       have r₂ := eq310725
       grind)
    | exact resolve eq1175 eq310725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175 eq310725
  have eq310757 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq310753
  have eq310758 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq310757
  have eq312049 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq310613
       have i₂ := eq310758
       grind)
    | exact superpose eq310758 eq310613
    | exact resolve eq310613 eq310758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310613 eq310758
  have eq312053 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq312049
  have eq312054 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq312053
  have eq312980 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq26751 y
       have i₂ := eq312054
       grind)
    | exact superpose eq312054 eq26751
    | exact resolve eq26751 eq312054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313075 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1350 y y
       have i₂ := eq312054
       grind)
    | exact superpose eq312054 eq1350
    | exact resolve eq1350 eq312054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312054
  have eq317454 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq312980
       grind)
    | exact superpose eq312980 eq16
    | exact resolve eq16 eq312980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312980
  have eq317587 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq317454
       have i₂ := eq313075
       grind)
    | exact superpose eq313075 eq317454
    | exact resolve eq317454 eq313075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313075 eq317454
  have eq317593 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq317587
  have eq317594 : (σ x) = (σ (M.op y y)) := by grind
  clear eq317593
  have eq318994 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26751 y
       have i₂ := eq317594
       grind)
    | exact superpose eq317594 eq26751
    | exact resolve eq26751 eq317594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26751
  have eq319019 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq317594
       grind)
    | exact superpose eq317594 eq10
    | exact resolve eq10 eq317594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317594
  have eq319393 : x = (M.op y y) := by
    first
    | (have i₁ := eq319019
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq319019
    | exact resolve eq319019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319019
  have eq319793 : x = (M.op x y) := by
    first
    | (have i₁ := eq1350 y y
       have i₂ := eq319393
       grind)
    | exact superpose eq319393 eq1350
    | exact resolve eq1350 eq319393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq319393
  have eq323385 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq318994
       grind)
    | exact superpose eq318994 eq16
    | exact resolve eq16 eq318994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318994
  have eq323510 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq323385
       have i₂ := eq319793
       grind)
    | exact superpose eq319793 eq323385
    | exact resolve eq323385 eq319793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319793 eq323385
  have eq323511 : False := by grind
  exact eq323511

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 x
       have i₂ := eq14 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq72
    | exact resolve eq72 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq78
    | exact resolve eq78 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq464 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq8816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq79 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8817 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq8816
    | exact resolve eq8816 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8816
  have eq8828 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8817
       have r₂ := eq29
       grind)
    | exact resolve eq8817 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8817
  have eq8834 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq8828 eq49
    | exact resolve eq49 eq8828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8836 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq8828
  have eq8839 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq8834
    | exact resolve eq8834 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8834
  have eq8846 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8839
  have eq8970 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq8846
       grind)
    | exact superpose eq8846 eq46
    | exact resolve eq46 eq8846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq8846
  have eq8988 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8970
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8970
    | exact resolve eq8970 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8970
  have eq9008 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8988 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq8988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8988
  have eq9009 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9008
  have eq9013 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq9009
    | exact resolve eq9009 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9009
  have eq9014 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq9013
  have eq9143 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq9014 eq49
    | exact resolve eq49 eq9014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9014
  have eq9148 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq9143
    | exact resolve eq9143 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9143
  have eq9149 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9148
  have eq9151 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9149 eq29
    | exact resolve eq29 eq9149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9149
  have eq9210 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq8836 eq79
    | exact resolve eq79 eq8836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq8836
  have eq9220 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq9210
  have eq9229 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9220
       have r₂ := eq9151
       grind)
    | exact resolve eq9220 eq9151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9220
  have eq9357 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49 y
       have i₂ := eq9229
       grind)
    | exact superpose eq9229 eq49
    | exact resolve eq49 eq9229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq9229
  have eq9363 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9357
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq9357
    | exact resolve eq9357 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9357
  have eq9366 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9363 eq31
    | exact resolve eq31 eq9363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9363
  have eq9473 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq9366
    | exact resolve eq9366 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9366
  have eq9474 : x = (M.op x y) ∨ x = y := by grind
  clear eq9473
  have eq9475 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq9474 eq22
    | exact resolve eq22 eq9474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9577 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq9475
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9475
    | exact resolve eq9475 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9475
  have eq9755 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq9577 eq9151
    | (have r₁ := eq9151
       have r₂ := eq9577
       grind)
    | exact resolve eq9151 eq9577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9151 eq9577
  have eq9756 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq9755
  have eq9757 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq9756
  have eq9812 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq9757 eq31
    | exact resolve eq31 eq9757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9757
  have eq9928 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq9812
    | exact resolve eq9812 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq9812
  have eq9982 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq9928 eq9474
    | exact resolve eq9474 eq9928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9474 eq9928
  have eq9983 : x = y := by grind
  clear eq9982
  have eq10156 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq9983
       grind)
    | exact superpose eq9983 eq20
    | exact resolve eq20 eq9983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq10157 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq9983
       grind)
    | exact superpose eq9983 eq26
    | exact resolve eq26 eq9983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9983
  have eq10260 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10157
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10157
    | exact resolve eq10157 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10157
  have eq10262 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10260 eq28
    | exact resolve eq28 eq10260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10260
  have eq10379 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq10156
       grind)
    | exact superpose eq10156 eq64
    | exact resolve eq64 eq10156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq10385 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq10156
  have eq10388 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq10379
    | exact resolve eq10379 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10379
  have eq10395 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq10721 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq10730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10262 eq10721
    | exact resolve eq10721 eq10262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10721
  have eq10742 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10730
       have r₂ := eq29
       grind)
    | exact resolve eq10730 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10730
  have eq10747 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10262 eq10742
    | exact resolve eq10742 eq10262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10742
  have eq10751 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10747 eq29
    | exact resolve eq29 eq10747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10754 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10747 eq10395
    | exact resolve eq10395 eq10747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10395 eq10747
  have eq11168 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10754 eq10388
    | exact resolve eq10388 eq10754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10388 eq10754
  have eq11181 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq11168
  have eq11188 : x = (M.op x y) := by
    first
    | (have r₁ := eq11181
       have r₂ := eq10751
       grind)
    | exact resolve eq11181 eq10751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10751 eq11181
  have eq11206 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq11188 eq22
    | exact resolve eq22 eq11188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq11261 : x = (k x x) := by
    first
    | exact superpose eq11188 eq10385
    | exact resolve eq10385 eq11188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10385 eq11188
  have eq11317 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11206
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11206
    | exact resolve eq11206 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11206
  have eq11572 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq464 x
       have i₂ := eq11261
       grind)
    | exact superpose eq11261 eq464
    | (have j0 := eq464 x
       grind)
    | exact resolve eq464 eq11261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq11261
  have eq11576 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11572
  have eq11584 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11576
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11576
    | exact resolve eq11576 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11576
  have eq11599 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10262 eq11584
    | exact resolve eq11584 eq10262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10262 eq11584
  have eq11612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11317 eq11599
    | exact resolve eq11599 eq11317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11317 eq11599
  have eq11625 : False := by grind
  exact eq11625

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq48
    | exact resolve eq48 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq48
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq55 X1
       grind)
    | exact superpose eq55 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq89 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq170 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq174 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq170 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq178 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq174 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq174 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq190 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       have j1 := eq89 X1 (σ X0)
       grind)
    | (have r₁ := eq178 X0 X0
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq178 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq178
  have eq197 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq190
    | (have j0 := eq190 X0 X1
       grind)
    | exact resolve eq190 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq198 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq204 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq198 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq198
    | exact resolve eq198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq198 x y
       grind)
    | exact superpose eq198 eq16
    | exact resolve eq16 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq290 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq204 X0 (τ X1)
       grind)
    | exact superpose eq204 eq18
    | exact resolve eq18 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq204
  have eq307 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq290
    | exact resolve eq290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq315 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq307
    | exact resolve eq307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq336 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq215
       have i₂ := eq315 x y
       grind)
    | exact superpose eq315 eq215
    | exact resolve eq215 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq315
  have eq337 : False := by grind
  exact eq337

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq80 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq81 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq80 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq96 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq81 (σ X0)
       grind)
    | exact superpose eq81 eq15
    | exact resolve eq15 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq81 (τ X0)
       grind)
    | exact superpose eq81 eq32
    | exact resolve eq32 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq105 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq98
    | exact resolve eq98 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq96
    | exact resolve eq96 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq96
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq213 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq107 X1
       grind)
    | exact superpose eq107 eq204
    | (have j0 := eq204 X0 X1
       grind)
    | exact resolve eq204 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq630 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq213 X1 (τ X0)
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq213
    | (have j0 := eq213 X1 (τ X0)
       grind)
    | exact resolve eq213 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq213
  have eq678 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq630
    | (have j0 := eq630 X0 X1
       grind)
    | exact resolve eq630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq680 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq678 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq678
    | (have j0 := eq678 X0 X1
       grind)
    | exact resolve eq678 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq681 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq680
    | (have j0 := eq680 X0 X1
       grind)
    | exact resolve eq680 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq682 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq681
    | (have j0 := eq681 X0 X1
       grind)
    | exact resolve eq681 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq683 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq682 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq682 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq682 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq684 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq683
    | (have j0 := eq683 X0 X1
       grind)
    | exact resolve eq683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq685 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq684
    | exact resolve eq684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq684 (σ X1) X0
       grind)
    | exact superpose eq684 eq15
    | (have j1 := eq684 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq726 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq685 X0 (τ X1)
       grind)
    | exact superpose eq685 eq19
    | (have j1 := eq685 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq685
  have eq840 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq726
    | exact resolve eq726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq887 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq840 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq840
    | (have j0 := eq840 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq840 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq1024 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq692 x y
       grind)
    | exact superpose eq692 eq16
    | (have j1 := eq692 x y
       grind)
    | exact resolve eq16 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq1041 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1024
       have i₂ := eq887 y x
       grind)
    | exact superpose eq887 eq1024
    | (have j1 := eq887 (σ x) (σ y)
       grind)
    | (have r₁ := eq1024
       have r₂ := eq887 y x
       grind)
    | (have r₁ := eq1024
       have r₂ := eq887 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1024
       have r₂ := eq887 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1024 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq1024
  have eq1042 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1041
  have eq1045 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1042
       grind)
    | exact superpose eq1042 eq16
    | exact resolve eq16 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1046 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1045
       have r₂ := eq107 x
       grind)
    | exact resolve eq1045 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1047 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq16
    | exact resolve eq16 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1048 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq10
    | exact resolve eq10 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1091 : x = y := by
    first
    | (have i₁ := eq1048
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1048
    | exact resolve eq1048 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1092 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1047
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq1047
    | exact resolve eq1047 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1047
  have eq1093 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1092
       have i₂ := eq1091
       grind)
    | exact superpose eq1091 eq1092
    | exact resolve eq1092 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq1092
  have eq1094 : False := by grind
  exact eq1094

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxx_pyx_Equation4494 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq179 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op x X1)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op X1 y) y) := by
    intro X1
    first
    | (have i₁ := eq16 x y X1
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op (M.op x y) y) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op y y) x
       have i₂ := eq180 (M.op y y)
       grind)
    | exact superpose eq180 eq13
    | (have r₁ := eq13 (M.op y y) (M.op (M.op x y) y)
       have r₂ := eq180 (M.op y y)
       grind)
    | exact resolve eq13 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X1 (σ y)) (σ y)) := by
    intro X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ X0 ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq181 eq13
    | (have r₁ := eq13 (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq181 (M.op (σ y) (σ y))
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : (σ (M.op y y)) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq37 (M.op y y)
       have i₂ := eq185 y
       grind)
    | exact superpose eq185 eq37
    | exact resolve eq37 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq248 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq185 sF2
       grind)
    | exact superpose eq185 eq91
    | exact resolve eq91 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq259 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq185 sF3
       grind)
    | exact superpose eq185 eq108
    | exact resolve eq108 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq185
  have eq432 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op y y) X0) ∨ (M.op (M.op x y) y) = X0 ∨ (M.op (M.op y y) (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op y y) X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq11
    | (have j0 := eq11 (M.op y y) X0
       grind)
    | exact resolve eq11 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) X0) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = X0 ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq181 eq11
    | (have j0 := eq11 (M.op (σ y) (σ y)) X0
       grind)
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq782 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 X1 X2 : G, (M.op X1 (k X0 X0)) = (M.op (M.op X2 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : ∀ X0 X1 X2 : G, (M.op X1 (k X0 X0)) = (M.op (M.op X2 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq786 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq848 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq787 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq787 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq787 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
       grind)
    | (have r₁ := eq787 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq787 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq850 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) X0) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq774 X0
       have j1 := eq201 X0
       grind)
    | (have r₁ := eq774 X0
       have r₂ := eq201 (k (M.op (σ y) (σ y)) X0)
       grind)
    | (have r₁ := eq774 X0
       have r₂ := eq201 X0
       grind)
    | (have r₁ := eq774 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq201 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq774 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq852 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op y y) X0) ∨ (M.op (M.op y y) (M.op y y)) = X0 := by
    intro X0
    first
    | (have j0 := eq772 X0
       have j1 := eq189 X0
       grind)
    | (have r₁ := eq772 X0
       have r₂ := eq189 (k (M.op y y) X0)
       grind)
    | (have r₁ := eq772 X0
       have r₂ := eq189 X0
       grind)
    | (have r₁ := eq772 (M.op (M.op x y) y)
       have r₂ := eq189 (M.op (M.op x y) y)
       grind)
    | exact resolve eq772 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq863 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq848 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq848 X0 (M.op X0 X0)
       have r₂ := eq28 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq848 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq848 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq865 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = X0 ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq181 eq850
    | (have j0 := eq850 X0
       grind)
    | exact resolve eq850 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq850
  have eq867 : ∀ X0 : G, (M.op (M.op x y) y) = X0 ∨ (M.op (M.op x y) y) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq852 X0
       have i₂ := eq180 (M.op y y)
       grind)
    | exact superpose eq180 eq852
    | (have j0 := eq852 X0
       grind)
    | exact resolve eq852 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq852
  have eq873 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq865 (k (M.op (σ y) (σ y)) X0)
       have j1 := eq201 X0
       grind)
    | (have r₁ := eq865 X0
       have r₂ := eq201 X0
       grind)
    | (have r₁ := eq865 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq201 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq865 X0
       have r₂ := eq201 (k (M.op (σ y) (σ y)) X0)
       grind)
    | exact resolve eq865 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq865
  have eq875 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have j0 := eq867 (k (M.op y y) X0)
       have j1 := eq189 X0
       grind)
    | (have r₁ := eq867 X0
       have r₂ := eq189 X0
       grind)
    | (have r₁ := eq867 (M.op (M.op x y) y)
       have r₂ := eq189 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq867 X0
       have r₂ := eq189 (k (M.op y y) X0)
       grind)
    | exact resolve eq867 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq867
  have eq896 : ∀ X0 : G, (k (σ (M.op y y)) X0) = (σ (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 (M.op y y)
       have i₂ := eq875 (τ X0)
       grind)
    | exact superpose eq875 eq39
    | exact resolve eq39 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1274 : (τ (M.op (σ y) (σ y))) ≠ (τ (M.op (σ y) (σ y))) ∨ (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq259 eq863
    | (have r₁ := eq863 y (τ (M.op (σ y) (σ y)))
       have r₂ := eq259
       grind)
    | exact resolve eq863 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1278 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq214 eq863
    | (have r₁ := eq863 (σ y) (σ (M.op y y))
       have r₂ := eq214
       grind)
    | exact resolve eq863 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq863
  have eq1279 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1278
  have eq1283 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by grind
  clear eq1274
  have eq1348 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X2 (M.op X1 X1)) ∨ (M.op X1 X1) = (k X1 (M.op X2 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 (M.op X2 (M.op X1 X1))
       have i₂ := eq179 X2 X1 X0
       grind)
    | exact superpose eq179 eq28
    | (have j0 := eq28 X1 (M.op X2 (M.op X1 X1))
       grind)
    | (have r₁ := eq28 (M.op X1 X1) (M.op (M.op X0 (M.op X1 X1)) X1)
       have r₂ := eq179 X0 X1 (M.op (M.op X0 (M.op X1 X1)) X1)
       grind)
    | (have r₁ := eq28 X1 (M.op X2 (M.op X1 X1))
       have r₂ := eq179 X2 X1 X2
       grind)
    | exact resolve eq28 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1368 : ∀ X1 X2 : G, (M.op X1 X1) = (k X1 (M.op X2 (M.op X1 X1))) := by
    intro X1 X2
    first
    | (have j0 := eq1348 x X1 X2
       grind)
    | (have r₁ := eq1348 x X1 X2
       have r₂ := eq182 x X1 X2
       grind)
    | (have r₁ := eq1348 X2 X1 x
       have r₂ := eq182 x X1 X2
       grind)
    | exact resolve eq1348 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1381 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1279
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq1279
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq1279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1385 : ∀ X0 : G, (k (M.op (σ y) (σ y)) X0) = (σ (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq896 X0
       have i₂ := eq1279
       grind)
    | exact superpose eq1279 eq896
    | exact resolve eq896 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq1397 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (τ (k (M.op (σ y) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq432 (M.op y y) X0
       have i₂ := eq1279
       grind)
    | exact superpose eq1279 eq432
    | exact resolve eq432 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq1398 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1381
  have eq1399 : ∀ X0 : G, (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (M.op y y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq873 eq1397
    | exact resolve eq1397 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1407 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq873 eq1385
    | exact resolve eq1385 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq1385
  have eq1411 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1398
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq1398
    | exact resolve eq1398 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1412 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq1399 x
       have i₂ := eq875 (τ x)
       grind)
    | exact superpose eq875 eq1399
    | exact resolve eq1399 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq1399
  have eq1418 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1411
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1411
    | exact resolve eq1411 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq1560 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X1 (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1368 X0 x
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq1368
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1368 X1 x
       have i₂ := eq16 x X1 X0
       grind)
    | exact superpose eq16 eq1368
    | exact resolve eq1368 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368
  have eq1600 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X1 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1560 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq1909 : (τ (k (σ y) (σ y))) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1418 eq1283
    | exact resolve eq1283 eq1418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq1418
  have eq1924 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq116 eq1909
    | exact resolve eq1909 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909
  have eq1930 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq1924
       have r₂ := eq13 y (k y y)
       grind)
    | (have r₁ := eq1924
       have r₂ := eq13 y y
       grind)
    | exact resolve eq1924 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924
  have eq1947 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1279
       have i₂ := eq1930
       grind)
    | exact superpose eq1930 eq1279
    | exact resolve eq1279 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq1962 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1947
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq1947
    | exact resolve eq1947 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq1968 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1962
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1962
    | exact resolve eq1962 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962
  have eq1979 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq781
       grind)
    | exact superpose eq781 eq40
    | exact resolve eq40 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq781
  have eq1981 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1979
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1979
    | exact resolve eq1979 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq1983 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1981
    | exact resolve eq1981 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq1985 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1983
       have i₂ := eq1930
       grind)
    | exact superpose eq1930 eq1983
    | exact resolve eq1983 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930 eq1983
  have eq3286 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (k X1 X1))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1564 x X1
       have i₂ := eq832 X1 X0 x
       grind)
    | exact superpose eq832 eq1564
    | (have j1 := eq832 X1 X1 x
       grind)
    | exact resolve eq1564 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq1564
  have eq3339 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | exact superpose eq1600 eq3286
    | (have j0 := eq3286 x X1
       have j1 := eq1600 X1 X1
       grind)
    | exact resolve eq3286 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600 eq3286
  have eq3374 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    first
    | (have j0 := eq3339 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq3339 x
       have r₂ := eq13 x (k x x)
       grind)
    | (have r₁ := eq3339 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq3339 (M.op x x)
       have r₂ := eq13 x (M.op (M.op x x) (M.op x x))
       grind)
    | exact resolve eq3339 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3339
  have eq3417 : ∀ X0 X1 X2 : G, (M.op X1 (k X0 X0)) = (M.op X2 (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X1 X2
       have i₂ := eq3374 X1
       grind)
    | exact superpose eq3374 eq182
    | exact resolve eq182 eq3374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq3421 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X1
       have i₂ := eq3374 X1
       grind)
    | exact superpose eq3374 eq16
    | exact resolve eq16 eq3374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374
  have eq4064 : ∀ X0 X1 X2 : G, (M.op X0 (k X1 X1)) ≠ X2 ∨ (M.op X0 (k X1 X1)) = (k (k X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 X0) X1
       have i₂ := eq3417 X0 (k X0 X0) X2
       grind)
    | (have i₁ := eq13 (k X0 X0) X1
       have i₂ := eq3417 X0 X1 (k X0 X0)
       grind)
    | exact superpose eq3417 eq13
    | (have r₁ := eq13 (k X0 X0) (M.op X2 (k X0 X0))
       have r₂ := eq3417 X0 (k X0 X0) X2
       grind)
    | (have r₁ := eq13 (k X0 X0) (M.op X1 (k X0 X0))
       have r₂ := eq3417 X0 X1 (k X0 X0)
       grind)
    | exact resolve eq13 eq3417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4072 : ∀ X0 X1 X2 : G, (M.op X0 (k X1 X1)) = (k (k X1 X1) X2) ∨ (M.op X0 (k X1 X1)) = X2 ∨ (M.op (k X1 X1) (k X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 X0) X1
       have i₂ := eq3417 X0 X1 X2
       grind)
    | (have i₁ := eq11 (k X0 X0) X2
       have i₂ := eq3417 X0 X1 X2
       grind)
    | exact superpose eq3417 eq11
    | (have j0 := eq11 (k X1 X1) X2
       grind)
    | exact resolve eq11 eq3417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3417
  have eq4094 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X1) = X2 ∨ (M.op X0 (k X1 X1)) = (k (k X1 X1) X2) ∨ (M.op X0 (k X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4072 X0 X1 X2
       have i₂ := eq3421 X1 (k X1 X1)
       grind)
    | exact superpose eq3421 eq4072
    | (have j0 := eq4072 X0 X1 X2
       grind)
    | exact resolve eq4072 eq3421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4072
  have eq4128 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X1) = X2 ∨ (M.op X0 (k X1 X1)) = (k (k X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4094 X0 X1 X2
       have j1 := eq4064 X0 X1 X2
       grind)
    | (have r₁ := eq4094 X0 (k X1 X1) X2
       have r₂ := eq4064 (k (k X1 X1) (k X1 X1)) X1 X2
       grind)
    | (have r₁ := eq4094 X0 X1 (M.op X0 (k X1 X1))
       have r₂ := eq4064 X0 X1 (M.op (k X1 X1) X1)
       grind)
    | (have r₁ := eq4094 X0 X1 X2
       have r₂ := eq4064 X0 X1 (k (k X1 X1) X2)
       grind)
    | exact resolve eq4094 eq4064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4064 eq4094
  have eq4338 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) ≠ X1 ∨ (M.op (k X0 X0) (k X0 X0)) = (k (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (k X0 X0) X1
       have i₂ := eq3421 X0 X1
       grind)
    | exact superpose eq3421 eq28
    | (have j0 := eq28 (k X0 X0) X1
       grind)
    | (have r₁ := eq28 (k X0 X0) (M.op (k X0 X0) X0)
       have r₂ := eq3421 X0 (M.op (k X0 X0) X0)
       grind)
    | exact resolve eq28 eq3421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4421 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X0 X0)) = (k (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq4338 X0 X1
       have j1 := eq4128 (k X0 X0) X0 X1
       grind)
    | (have r₁ := eq4338 X1 x
       have r₂ := eq4128 X0 X1 x
       grind)
    | (have r₁ := eq4338 X0 (M.op (k X1 X1) X1)
       have r₂ := eq4128 X0 X1 (M.op (k X0 X0) X0)
       grind)
    | (have r₁ := eq4338 (k X1 X1) (k (k X1 X1) x)
       have r₂ := eq4128 (k (k X1 X1) (k X1 X1)) X1 x
       grind)
    | exact resolve eq4338 eq4128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4128 eq4338
  have eq4461 : ∀ X0 X1 : G, (k (k X0 X0) X1) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4421 X0 X1
       have i₂ := eq3421 X0 (k X0 X0)
       grind)
    | exact superpose eq3421 eq4421
    | exact resolve eq4421 eq3421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4421
  have eq8957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1985 eq782
    | exact resolve eq782 eq1985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq1985
  have eq8968 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8957
       have r₂ := eq27
       grind)
    | exact resolve eq8957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8957
  have eq8973 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1968 eq8968
    | exact resolve eq8968 eq1968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968 eq8968
  have eq8975 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8973 eq116
    | exact resolve eq116 eq8973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq8973
  have eq9028 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq8975
    | exact resolve eq8975 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8975
  have eq9029 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9028
  have eq9052 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq9029
       grind)
    | exact superpose eq9029 eq41
    | exact resolve eq41 eq9029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq9063 : ∀ X0 : G, (M.op x y) = (k x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4461 y x
       have i₂ := eq9029
       grind)
    | exact superpose eq9029 eq4461
    | exact resolve eq4461 eq9029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4461 eq9029
  have eq9074 : ∀ X0 : G, (M.op x y) = (k x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9063 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9063
    | (have j0 := eq9063 X0
       grind)
    | exact resolve eq9063 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9063
  have eq9080 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9052
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9052
    | exact resolve eq9052 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9052
  have eq9087 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9080
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9080
    | exact resolve eq9080 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9080
  have eq9118 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9087 eq3421
    | exact resolve eq3421 eq9087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421 eq9087
  have eq9133 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq9118
    | (have j0 := eq9118 X0
       grind)
    | exact resolve eq9118 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9118
  have eq10143 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9133 eq248
    | exact resolve eq248 eq9133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq9133
  have eq10144 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9074 eq10143
    | exact resolve eq10143 eq9074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9074 eq10143
  have eq10229 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10144 eq14
    | exact resolve eq14 eq10144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10144
  have eq10230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq10229
    | exact resolve eq10229 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10229
  have eq10234 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10230
       have r₂ := eq27
       grind)
    | exact resolve eq10230 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10230
  have eq10251 : (M.op (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10234 eq1412
    | exact resolve eq1412 eq10234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq10261 : (M.op (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10251
    | exact resolve eq10251 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10251
  have eq10279 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10234 eq10261
    | exact resolve eq10261 eq10234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10234 eq10261
  have eq10293 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq10279
    | exact resolve eq10279 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10279
  have eq10554 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10293 eq188
    | exact resolve eq188 eq10293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq10293
  have eq10582 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10554
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10554
    | exact resolve eq10554 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10554
  have eq10583 : x = (M.op x y) := by grind
  clear eq10582
  have eq10604 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10583
       grind)
    | exact superpose eq10583 eq18
    | exact resolve eq18 eq10583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq10605 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq10583
       grind)
    | exact superpose eq10583 eq22
    | exact resolve eq22 eq10583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10583
  have eq10646 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10605 eq20
    | exact resolve eq20 eq10605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10605
  have eq10752 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq10604 eq1407
    | exact resolve eq1407 eq10604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407 eq10604
  have eq10778 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq20 eq10752
    | exact resolve eq10752 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10752
  have eq10785 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq10646 eq10778
    | exact resolve eq10778 eq10646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10778
  have eq11038 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10785 eq200
    | exact resolve eq200 eq10785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq10785
  have eq11399 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11038 eq26
    | exact resolve eq26 eq11038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11038
  have eq11446 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq11399 eq27
    | exact resolve eq27 eq11399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11399
  have eq11485 : False := by grind
  exact eq11485

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pxy_pyx_Equation4494 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq55 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 y x
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq9 X2 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq68 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq87 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op y y) (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op y y) x
       have i₂ := eq55 (M.op x (M.op y y))
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq55 (M.op y y)
       grind)
    | exact superpose eq55 eq87
    | exact resolve eq87 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq139 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq89 eq12
    | (have j0 := eq12 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op x y) y)
       have r₂ := eq89 (M.op (M.op x y) y)
       grind)
    | exact resolve eq12 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have j0 := eq139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq166 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (M.op (M.op x y) y)))) := by
    intro X0
    first
    | (have i₁ := eq143 (σ x)
       have i₂ := eq48 (M.op sF0 y) x
       grind)
    | exact superpose eq48 eq143
    | exact resolve eq143 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq210 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq166 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq166
    | exact resolve eq166 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq243 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq143 eq210
    | exact resolve eq210 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq210
  have eq480 : (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq89 eq243
    | exact resolve eq243 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq481 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (M.op (σ y) (σ y))) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq60 eq243
    | exact resolve eq243 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (k (τ (σ y)) (τ (M.op (M.op x y) y))) (τ (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq481
       have i₂ := eq243 sF3
       grind)
    | exact superpose eq243 eq481
    | exact resolve eq481 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq501 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (k y (τ (M.op (M.op x y) y))) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq39 eq494
    | exact resolve eq494 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq641 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq63
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq63
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq652 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq641
    | exact resolve eq641 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq4577 : (τ (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) ∨ (τ (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) ∨ (τ (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq480 eq14
    | (have j0 := eq14 (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))
       grind)
    | exact resolve eq14 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq4579 : (τ (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by grind
  clear eq4577
  have eq4587 : ∀ X0 : G, (τ (M.op (M.op x y) y)) ≠ (τ (M.op (M.op x y) y)) ∨ (M.op X0 X0) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq4579 eq12
    | (have j0 := eq12 X0 (τ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq12 X0 (τ (M.op (M.op x y) y))
       have r₂ := eq4579
       grind)
    | exact resolve eq12 eq4579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4579
  have eq4621 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have j0 := eq4587 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq4631 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq4621 eq176
    | exact resolve eq176 eq4621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq4645 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq4621 eq243
    | exact resolve eq243 eq4621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq4680 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (k y (τ (M.op (M.op x y) y))) (k y (τ (M.op (M.op x y) y)))) := by
    first
    | exact superpose eq4621 eq501
    | exact resolve eq501 eq4621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq4696 : (M.op (M.op y y) (M.op y y)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq4621 eq4680
    | exact resolve eq4680 eq4621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4621 eq4680
  have eq4790 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq4696
       have i₂ := eq55 (M.op y y)
       grind)
    | exact superpose eq55 eq4696
    | exact resolve eq4696 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq4696
  have eq4999 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq4790 eq11
    | exact resolve eq11 eq4790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4790
  have eq29599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq652
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq652
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq652 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq29635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29599
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29599
    | exact resolve eq29599 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29599
  have eq29638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq29635
    | exact resolve eq29635 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29635
  have eq29639 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29638
       have r₂ := eq27
       grind)
    | exact resolve eq29638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29638
  have eq29696 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29639 eq4645
    | exact resolve eq4645 eq29639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29639
  have eq29744 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39 eq29696
    | exact resolve eq29696 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29696
  have eq29745 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq29744
  have eq29806 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29745 eq4645
    | exact resolve eq4645 eq29745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29745
  have eq29846 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq29806
    | exact resolve eq29806 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq29806
  have eq29847 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq29846
  have eq29867 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 y x
       have i₂ := eq29847
       grind)
    | exact superpose eq29847 eq58
    | exact resolve eq58 eq29847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29898 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4631 y
       have i₂ := eq29847
       grind)
    | exact superpose eq29847 eq4631
    | exact resolve eq4631 eq29847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29847
  have eq29944 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29898
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29898
    | exact resolve eq29898 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29898
  have eq29976 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq29944 eq58
    | exact resolve eq58 eq29944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq29944
  have eq30404 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq29867 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq29867 X0 x
       grind)
    | exact superpose eq29867 eq18
    | (have j1 := eq29867 x X0
       grind)
    | exact resolve eq18 eq29867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29867
  have eq30696 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4999
       have i₂ := eq30404 sF0
       grind)
    | exact superpose eq30404 eq4999
    | exact resolve eq4999 eq30404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30404
  have eq30781 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq30696
    | exact resolve eq30696 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30696
  have eq53393 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29976 eq26
    | (have j1 := eq29976 (σ x) X0
       grind)
    | exact resolve eq26 eq29976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29976
  have eq53811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq53393 eq30781
    | exact resolve eq30781 eq53393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30781 eq53393
  have eq53911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq53811
  have eq53933 : x = (M.op x x) := by
    first
    | (have r₁ := eq53911
       have r₂ := eq27
       grind)
    | exact resolve eq53911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53911
  have eq56020 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq53933
       grind)
    | exact superpose eq53933 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq53933
       grind)
    | exact resolve eq13 eq53933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56060 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4631 x
       have i₂ := eq53933
       grind)
    | exact superpose eq53933 eq4631
    | exact resolve eq4631 eq53933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53933
  have eq56096 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq56020 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56020
  have eq56185 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56060
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56060
    | exact resolve eq56060 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq56060
  have eq60667 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq56185 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq56185
       grind)
    | exact resolve eq13 eq56185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56185
  have eq60743 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq60667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60667
  have eq67504 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq60743 eq68
    | (have j1 := eq60743 (σ y)
       grind)
    | exact resolve eq68 eq60743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq60743
  have eq67509 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq67504
    | exact resolve eq67504 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67504
  have eq67537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq67509
       have i₂ := eq56096 y
       grind)
    | exact superpose eq56096 eq67509
    | (have j1 := eq56096 (σ y)
       grind)
    | exact resolve eq67509 eq56096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56096 eq67509
  have eq67578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq67537
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq67537
    | exact resolve eq67537 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67537
  have eq67584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq67578
    | exact resolve eq67578 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67578
  have eq67590 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq67584
       have r₂ := eq27
       grind)
    | exact resolve eq67584 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67584
  have eq67652 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq67590 eq4645
    | exact resolve eq4645 eq67590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645 eq67590
  have eq67702 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq39 eq67652
    | exact resolve eq67652 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq67652
  have eq67703 : y = (M.op y y) := by grind
  clear eq67702
  have eq67898 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4631 y
       have i₂ := eq67703
       grind)
    | exact superpose eq67703 eq4631
    | exact resolve eq4631 eq67703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4631
  have eq67902 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq67703
       grind)
    | exact superpose eq67703 eq9
    | exact resolve eq9 eq67703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67952 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq67902 X0
       have i₂ := eq67703
       grind)
    | exact superpose eq67703 eq67902
    | exact resolve eq67902 eq67703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67703 eq67902
  have eq67969 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq67898
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq67898
    | exact resolve eq67898 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67898
  have eq68807 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq67952 x
       grind)
    | exact superpose eq67952 eq18
    | (have j1 := eq67952 x
       grind)
    | exact resolve eq18 eq67952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq68810 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq4999
       have i₂ := eq67952 sF0
       grind)
    | exact superpose eq67952 eq4999
    | exact resolve eq4999 eq67952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4999 eq67952
  have eq68926 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq67969 eq60
    | exact resolve eq60 eq67969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq67969
  have eq69483 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq68810
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq68810
    | exact resolve eq68810 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68810
  have eq69484 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq68807 eq20
    | exact resolve eq20 eq68807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq68807
  have eq71005 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq69483 eq68926
    | exact resolve eq68926 eq69483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68926 eq69483
  have eq71507 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq69484
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq69484
    | exact resolve eq69484 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq69484
  have eq71773 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71005 eq26
    | (have j1 := eq71005 (σ x)
       grind)
    | exact resolve eq26 eq71005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq71005
  have eq72718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71507 eq71773
    | exact resolve eq71773 eq71507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71507 eq71773
  have eq73381 : False := by grind
  exact eq73381
