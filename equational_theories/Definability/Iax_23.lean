import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation432`: `x = x ◇ (y ◇ (x ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation432 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law432 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law432.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = X0 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X0
       have i₂ := eq8 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X0)
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
  clear eq16
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
  have eq59 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq26 (τ X0) X1
       grind)
    | exact superpose eq26 eq17
    | (have j1 := eq26 (τ X0) X1
       grind)
    | exact resolve eq17 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq26 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq97 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq99 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq44
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq111 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq140 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (M.op X0 X1)
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq62
    | (have j0 := eq62 X1 X0
       grind)
    | exact resolve eq62 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq166 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X0)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq19
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq19 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq234 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq111
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq111 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq111
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq234
    | (have j0 := eq234 X0 X1
       grind)
    | exact resolve eq234 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq605 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
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
  clear eq39
  have eq681 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq605
    | (have j0 := eq605 X0 X1
       grind)
    | exact resolve eq605 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq706 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59
    | exact resolve eq59 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq749 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq706 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq706
    | (have j0 := eq706 X0 X1
       grind)
    | exact resolve eq706 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq1014 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X1)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq19
    | (have j1 := eq56 X0 X1
       grind)
    | exact resolve eq19 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1499 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq181 x y
       grind)
    | exact superpose eq181 eq14
    | (have j1 := eq181 x y
       grind)
    | exact resolve eq14 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1515 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2080 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq166 (τ X1) (τ X0)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq166
    | (have j0 := eq166 (τ X0) (τ X1)
       grind)
    | exact resolve eq166 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq166
  have eq2129 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2080 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2080
    | (have j0 := eq2080 X0 X1
       grind)
    | exact resolve eq2080 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq2133 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2129 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2129
    | (have j0 := eq2129 X0 X1
       grind)
    | exact resolve eq2129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129
  have eq2134 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2133 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2133
    | (have j0 := eq2133 X0 X1
       grind)
    | exact resolve eq2133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2135 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2134 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2134
    | (have j0 := eq2134 X0 X1
       grind)
    | exact resolve eq2134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134
  have eq10389 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq255 x y
       grind)
    | exact superpose eq255 eq14
    | (have j1 := eq255 x y
       grind)
    | exact resolve eq14 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq10424 : y = (k y x) := by
    first
    | (have j1 := eq749 x y
       grind)
    | (have r₁ := eq10389
       have r₂ := eq749 x y
       grind)
    | exact resolve eq10389 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq10389
  have eq10961 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq681 x y
       have i₂ := eq10424
       grind)
    | exact superpose eq10424 eq681
    | (have j0 := eq681 x y
       grind)
    | exact resolve eq681 eq10424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10963 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1515 x y
       have i₂ := eq10424
       grind)
    | exact superpose eq10424 eq1515
    | (have j0 := eq1515 x y
       grind)
    | exact resolve eq1515 eq10424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10964 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2135 y x
       have i₂ := eq10424
       grind)
    | exact superpose eq10424 eq2135
    | (have j0 := eq2135 y y
       grind)
    | exact resolve eq2135 eq10424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135
  have eq12030 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq140 y y
       have i₂ := eq10964
       grind)
    | exact superpose eq10964 eq140
    | (have r₁ := eq140 y y
       have r₂ := eq10964
       grind)
    | exact resolve eq140 eq10964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq12034 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq10964
  have eq12035 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq12030
  have eq13347 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1515 y y
       have i₂ := eq12035
       grind)
    | exact superpose eq12035 eq1515
    | (have j0 := eq1515 y y
       grind)
    | exact resolve eq1515 eq12035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515 eq12035
  have eq13352 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq13347
  have eq21632 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1499
       have i₂ := eq681 x y
       grind)
    | exact superpose eq681 eq1499
    | (have j1 := eq681 x y
       grind)
    | (have r₁ := eq1499
       have r₂ := eq681 x y
       grind)
    | exact resolve eq1499 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq1499
  have eq21641 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq21632
  have eq21899 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21641
       grind)
    | exact superpose eq21641 eq14
    | exact resolve eq14 eq21641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21911 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99 (σ x) y
       have i₂ := eq21641
       grind)
    | exact superpose eq21641 eq99
    | (have j0 := eq99 (σ x) y
       grind)
    | exact resolve eq99 eq21641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq21641
  have eq21956 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21911
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq21911
    | exact resolve eq21911 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21911
  have eq21978 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21956
       have i₂ := eq10424
       grind)
    | exact superpose eq10424 eq21956
    | exact resolve eq21956 eq10424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10424 eq21956
  have eq21983 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq21978
       have r₂ := eq12034
       grind)
    | exact resolve eq21978 eq12034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034 eq21978
  have eq22327 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21899
       have i₂ := eq10961
       grind)
    | exact superpose eq10961 eq21899
    | exact resolve eq21899 eq10961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10961 eq21899
  have eq22329 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq22327
  have eq24031 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13352
       have i₂ := eq21983
       grind)
    | exact superpose eq21983 eq13352
    | exact resolve eq13352 eq21983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13352 eq21983
  have eq24103 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq24031
  have eq24134 : x = (M.op y y) := by
    first
    | (have r₁ := eq24103
       have r₂ := eq22329
       grind)
    | exact resolve eq24103 eq22329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22329 eq24103
  have eq24595 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq8 y X0 y
       have i₂ := eq24134
       grind)
    | exact superpose eq24134 eq8
    | exact resolve eq8 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24597 : x = (M.op x y) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq24134
       grind)
    | exact superpose eq24134 eq19
    | exact resolve eq19 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq24598 : ∀ X0 : G, y = (M.op y (M.op X0 x)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq28 y y x
       have i₂ := eq24134
       grind)
    | exact superpose eq24134 eq28
    | exact resolve eq28 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq29726 : y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq24595 y
       have i₂ := eq24598 y
       grind)
    | exact superpose eq24598 eq24595
    | exact resolve eq24595 eq24598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24595 eq24598
  have eq29762 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq29726
       have i₂ := eq24134
       grind)
    | exact superpose eq24134 eq29726
    | exact resolve eq29726 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24134 eq29726
  have eq30441 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1014 y y
       have i₂ := eq29762
       grind)
    | exact superpose eq29762 eq1014
    | exact resolve eq1014 eq29762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq29762
  have eq30461 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq30441
       have r₂ := eq10963
       grind)
    | exact resolve eq30441 eq10963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30441
  have eq30983 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq30461
       grind)
    | exact superpose eq30461 eq14
    | exact resolve eq14 eq30461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30461
  have eq31050 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq30983
       have i₂ := eq24597
       grind)
    | exact superpose eq24597 eq30983
    | exact resolve eq30983 eq24597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30983
  have eq31051 : x = y := by grind
  clear eq31050
  have eq31680 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31051
       grind)
    | exact superpose eq31051 eq14
    | exact resolve eq14 eq31051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31688 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10963
       have i₂ := eq31051
       grind)
    | exact superpose eq31051 eq10963
    | exact resolve eq10963 eq31051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10963
  have eq31726 : x = (M.op x x) := by
    first
    | (have i₁ := eq24597
       have i₂ := eq31051
       grind)
    | exact superpose eq31051 eq24597
    | exact resolve eq24597 eq31051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24597 eq31051
  have eq31740 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31688
  have eq31746 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31680
       have i₂ := eq31726
       grind)
    | exact superpose eq31726 eq31680
    | exact resolve eq31680 eq31726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31680 eq31726
  have eq31747 : False := by grind
  exact eq31747

/-- `Equation432`: `x = x ◇ (y ◇ (x ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation432 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law432 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law432.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X0
       have i₂ := eq8 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X2 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35
    | exact resolve eq35 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq52 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq35
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq57 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50
    | exact resolve eq50 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
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
  have eq63 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq26 (τ X0) X1
       grind)
    | exact superpose eq26 eq16
    | (have j1 := eq26 (τ X0) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq140 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq64
    | (have j0 := eq64 X0 X1
       grind)
    | exact resolve eq64 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq166 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X0)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq19
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq19 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq234 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq57
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq57 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq57
  have eq255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq234
    | (have j0 := eq234 X0 X1
       grind)
    | exact resolve eq234 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq605 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq681 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq605
    | (have j0 := eq605 X0 X1
       grind)
    | exact resolve eq605 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq706 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq749 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq706 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq706
    | (have j0 := eq706 X0 X1
       grind)
    | exact resolve eq706 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq1014 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X0)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq19
    | (have j1 := eq58 X0 X1
       grind)
    | exact resolve eq19 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1500 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq181 x y
       grind)
    | exact superpose eq181 eq14
    | (have j1 := eq181 x y
       grind)
    | exact resolve eq14 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1516 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2118 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq166 (τ X1) (τ X0)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq166
    | (have j0 := eq166 (τ X0) (τ X1)
       grind)
    | exact resolve eq166 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq166
  have eq2175 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2118 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2118
    | (have j0 := eq2118 X0 X1
       grind)
    | exact resolve eq2118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2177 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2175 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2175
    | (have j0 := eq2175 X0 X1
       grind)
    | exact resolve eq2175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2178 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2177 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2177
    | (have j0 := eq2177 X0 X1
       grind)
    | exact resolve eq2177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq2179 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2178 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2178
    | (have j0 := eq2178 X0 X1
       grind)
    | exact resolve eq2178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq8966 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq255 x y
       grind)
    | exact superpose eq255 eq14
    | (have j1 := eq255 x y
       grind)
    | exact resolve eq14 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq8999 : y = (k x y) := by
    first
    | (have j1 := eq749 x y
       grind)
    | (have r₁ := eq8966
       have r₂ := eq749 x y
       grind)
    | exact resolve eq8966 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq8966
  have eq9612 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq681 x y
       have i₂ := eq8999
       grind)
    | exact superpose eq8999 eq681
    | (have j0 := eq681 x y
       grind)
    | exact resolve eq681 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9614 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1516 x y
       have i₂ := eq8999
       grind)
    | exact superpose eq8999 eq1516
    | (have j0 := eq1516 x y
       grind)
    | exact resolve eq1516 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9615 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2179 x y
       have i₂ := eq8999
       grind)
    | exact superpose eq8999 eq2179
    | (have j0 := eq2179 y y
       grind)
    | exact resolve eq2179 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179
  have eq11150 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq140 y y
       have i₂ := eq9615
       grind)
    | exact superpose eq9615 eq140
    | (have r₁ := eq140 y y
       have r₂ := eq9615
       grind)
    | exact resolve eq140 eq9615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq11154 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq9615
  have eq11155 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq11150
  have eq12205 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1516 y y
       have i₂ := eq11155
       grind)
    | exact superpose eq11155 eq1516
    | (have j0 := eq1516 y y
       grind)
    | exact resolve eq1516 eq11155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516 eq11155
  have eq12210 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq12205
  have eq21702 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1500
       have i₂ := eq681 x y
       grind)
    | exact superpose eq681 eq1500
    | (have j1 := eq681 x y
       grind)
    | (have r₁ := eq1500
       have r₂ := eq681 x y
       grind)
    | exact resolve eq1500 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq1500
  have eq21711 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq21702
  have eq21964 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21711
       grind)
    | exact superpose eq21711 eq14
    | exact resolve eq14 eq21711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21977 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 (σ x) y
       have i₂ := eq21711
       grind)
    | exact superpose eq21711 eq52
    | (have j0 := eq52 (σ x) y
       grind)
    | exact resolve eq52 eq21711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq21711
  have eq22020 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21977
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq21977
    | exact resolve eq21977 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21977
  have eq22042 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22020
       have i₂ := eq8999
       grind)
    | exact superpose eq8999 eq22020
    | exact resolve eq22020 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8999 eq22020
  have eq22047 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22042
       have r₂ := eq11154
       grind)
    | exact resolve eq22042 eq11154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11154 eq22042
  have eq22402 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21964
       have i₂ := eq9612
       grind)
    | exact superpose eq9612 eq21964
    | exact resolve eq21964 eq9612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9612 eq21964
  have eq22404 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq22402
  have eq24130 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12210
       have i₂ := eq22047
       grind)
    | exact superpose eq22047 eq12210
    | exact resolve eq12210 eq22047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12210 eq22047
  have eq24201 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq24130
  have eq24231 : x = (M.op y y) := by
    first
    | (have r₁ := eq24201
       have r₂ := eq22404
       grind)
    | exact resolve eq24201 eq22404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22404 eq24201
  have eq24703 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq8 y X0 y
       have i₂ := eq24231
       grind)
    | exact superpose eq24231 eq8
    | exact resolve eq8 eq24231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24705 : x = (M.op x y) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq24231
       grind)
    | exact superpose eq24231 eq19
    | exact resolve eq19 eq24231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq24706 : ∀ X0 : G, y = (M.op y (M.op X0 x)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq28 y y x
       have i₂ := eq24231
       grind)
    | exact superpose eq24231 eq28
    | exact resolve eq28 eq24231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq29170 : y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq24703 y
       have i₂ := eq24706 y
       grind)
    | exact superpose eq24706 eq24703
    | exact resolve eq24703 eq24706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24703 eq24706
  have eq29206 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq29170
       have i₂ := eq24231
       grind)
    | exact superpose eq24231 eq29170
    | exact resolve eq29170 eq24231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24231 eq29170
  have eq29879 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1014 y y
       have i₂ := eq29206
       grind)
    | exact superpose eq29206 eq1014
    | exact resolve eq1014 eq29206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq29206
  have eq29899 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq29879
       have r₂ := eq9614
       grind)
    | exact resolve eq29879 eq9614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29879
  have eq30555 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq29899
       grind)
    | exact superpose eq29899 eq14
    | exact resolve eq14 eq29899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29899
  have eq30622 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq30555
       have i₂ := eq24705
       grind)
    | exact superpose eq24705 eq30555
    | exact resolve eq30555 eq24705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30555
  have eq30623 : x = y := by grind
  clear eq30622
  have eq31245 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30623
       grind)
    | exact superpose eq30623 eq14
    | exact resolve eq14 eq30623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31253 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9614
       have i₂ := eq30623
       grind)
    | exact superpose eq30623 eq9614
    | exact resolve eq9614 eq30623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9614
  have eq31290 : x = (M.op x x) := by
    first
    | (have i₁ := eq24705
       have i₂ := eq30623
       grind)
    | exact superpose eq30623 eq24705
    | exact resolve eq24705 eq30623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24705 eq30623
  have eq31303 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31253
  have eq31309 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31245
       have i₂ := eq31290
       grind)
    | exact superpose eq31290 eq31245
    | exact resolve eq31245 eq31290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31245 eq31290
  have eq31310 : False := by grind
  exact eq31310

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation433 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law433 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq109 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq109 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq109 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq129 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq113 (σ X0) (σ X1)
       grind)
    | exact superpose eq113 eq13
    | exact resolve eq13 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 X1
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq129
    | exact resolve eq129 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq129
  have eq1291 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq136 x y
       grind)
    | exact superpose eq136 eq14
    | (have r₁ := eq14
       have r₂ := eq136 x y
       grind)
    | exact resolve eq14 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1320 : False := by grind
  exact eq1320

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxy_pyx_Equation433 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law433 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq8 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X2 X0) X0
       have i₂ := eq23 X2 X0
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq11
    | (have r₁ := eq11 X1 (M.op X0 X1)
       have r₂ := eq23 X0 X1
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq51 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq16
  have eq114 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq142 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq8
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq8 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) (σ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq23
    | (have j1 := eq38 (k X0 X1) X0
       grind)
    | exact resolve eq23 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq23
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq23 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq176 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (M.op X1 (σ X0))
       have i₂ := eq30 (σ X0) X1
       grind)
    | exact superpose eq30 eq56
    | exact resolve eq56 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq191 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq176
    | exact resolve eq176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq219 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op (M.op X1 X2) (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq27 X2 X0 X1
       grind)
    | exact superpose eq27 eq23
    | exact resolve eq23 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq936 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq983 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq936 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq936
    | (have j0 := eq936 X0 X1
       grind)
    | exact resolve eq936 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq1280 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq146 (τ X0) (τ X1)
       have i₂ := eq114 X1 X0
       grind)
    | exact superpose eq114 eq146
    | (have j0 := eq146 (τ X0) (τ (k X0 X1))
       grind)
    | exact resolve eq146 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq146
  have eq1323 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1280 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1280
    | (have j0 := eq1280 X0 X1
       grind)
    | exact resolve eq1280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1332 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1323 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1323
    | (have j0 := eq1323 X0 X1
       grind)
    | exact resolve eq1323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1333 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1332 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1332
    | (have j0 := eq1332 X0 X1
       grind)
    | exact resolve eq1332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1334 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1333 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1333
    | (have j0 := eq1333 X0 X1
       grind)
    | exact resolve eq1333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1345 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1334 X0 (τ (M.op X1 (σ X0)))
       have i₂ := eq191 X0 X1
       grind)
    | exact superpose eq191 eq1334
    | (have j0 := eq1334 X0 (τ (M.op X1 (σ X0)))
       grind)
    | exact resolve eq1334 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq1334
  have eq1401 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq155 y x
       grind)
    | exact superpose eq155 eq14
    | (have j1 := eq155 y x
       grind)
    | exact resolve eq14 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq1787 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (M.op X1 (σ X0)))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq142 X0 (M.op X2 X0) X1
       have i₂ := eq30 X0 X2
       grind)
    | exact superpose eq30 eq142
    | (have j0 := eq142 X0 (M.op X2 X0) X2
       grind)
    | exact resolve eq142 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq142
  have eq1898 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1787 X0 X1 X2
       have i₂ := eq23 X1 (σ X0)
       grind)
    | exact superpose eq23 eq1787
    | (have j0 := eq1787 X0 X1 X2
       grind)
    | exact resolve eq1787 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq5664 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1898 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1898
    | (have j0 := eq1898 (M.op X1 (τ X0)) X0 X2
       grind)
    | exact resolve eq1898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq9910 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1401
       have i₂ := eq983 x y
       grind)
    | exact superpose eq983 eq1401
    | (have j1 := eq983 (σ y) (σ x)
       grind)
    | (have r₁ := eq1401
       have r₂ := eq983 x y
       grind)
    | exact resolve eq1401 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983 eq1401
  have eq9911 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq9910
  have eq16410 : y = (M.op y (τ (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1345 y (σ x)
       have i₂ := eq9911
       grind)
    | exact superpose eq9911 eq1345
    | (have j0 := eq1345 y x
       grind)
    | exact resolve eq1345 eq9911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345 eq9911
  have eq16510 : y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16410
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq16410
    | exact resolve eq16410 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16410
  have eq16511 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq16510
  have eq17409 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op y (M.op X0 y)) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq219 X0 y y
       have i₂ := eq16511
       grind)
    | exact superpose eq16511 eq219
    | exact resolve eq219 eq16511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq16511
  have eq17480 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq17409 X0
       have i₂ := eq23 X0 y
       grind)
    | exact superpose eq23 eq17409
    | exact resolve eq17409 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17409
  have eq22040 : y ≠ y ∨ y = (M.op y x) := by
    first
    | (have j0 := eq17480 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17480
  have eq22041 : y = (M.op y x) := by grind
  clear eq22040
  have eq22388 : x = (M.op x y) := by
    first
    | (have i₁ := eq23 y x
       have i₂ := eq22041
       grind)
    | exact superpose eq22041 eq23
    | exact resolve eq23 eq22041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105846 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X1 (σ (M.op X2 (τ X1)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq5664 X1 X2 X0
       grind)
    | exact superpose eq5664 eq23
    | (have j1 := eq5664 X1 X2 X2
       grind)
    | exact resolve eq23 eq5664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5664
  have eq125406 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (σ (M.op X1 (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq105846 (σ (M.op X1 (τ X0))) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105846
  have eq125407 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq125406 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125406
  have eq126817 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq125407 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq125407
    | exact resolve eq125407 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125407
  have eq128374 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq126817 x y
       have i₂ := eq22041
       grind)
    | exact superpose eq22041 eq126817
    | exact resolve eq126817 eq22041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22041 eq126817
  have eq129876 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq128374
       grind)
    | exact superpose eq128374 eq14
    | exact resolve eq14 eq128374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128374
  have eq130150 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq129876
       have i₂ := eq22388
       grind)
    | exact superpose eq22388 eq129876
    | exact resolve eq129876 eq22388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22388 eq129876
  have eq130151 : False := by grind
  exact eq130151

/-- `Equation4331`: `x ◇ (y ◇ x) = z ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4331 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4331 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4331.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X2) X2 X3
       have i₂ := eq8 X2 X1 X0
       grind)
    | (have i₁ := eq8 (M.op X1 X1) X2 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | (have i₁ := eq8 X0 X0 X0
       have i₂ := eq8 X0 X0 X2
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
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  clear eq15
  have eq37 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq142 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq37 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq37 eq13
    | (have j1 := eq37 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq285 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (M.op X1 X1) X2 X3
       have i₂ := eq17 X2 X1 X1 X0
       grind)
    | (have i₁ := eq23 X2 X2 X2
       have i₂ := eq17 X0 X1 X2 X2
       grind)
    | exact superpose eq17 eq23
    | exact resolve eq23 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq23
  have eq351 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq285 x X1 X3 X2
       grind)
    | (have i₁ := eq8 X0 X3 X3
       have i₂ := eq285 X0 X1 X3 X3
       grind)
    | exact superpose eq285 eq8
    | exact resolve eq8 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq1104 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq35 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq35 X0 X1
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1163 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1104 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1104 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1971 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1163 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1163
    | (have j0 := eq1163 (τ X0) X1
       grind)
    | exact resolve eq1163 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1980 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1971 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1971
    | (have j0 := eq1971 X0 X1
       grind)
    | exact resolve eq1971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq1985 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1980 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1980
    | (have j0 := eq1980 X0 X1
       grind)
    | exact resolve eq1980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2004 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1985 (τ X0) X1
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq1985
    | (have j0 := eq1985 (τ X0) X1
       grind)
    | exact resolve eq1985 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1985
  have eq2804 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq2929 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2804 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2804
    | (have j0 := eq2804 X0 X1
       grind)
    | exact resolve eq2804 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq11293 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1159 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1159
    | (have j0 := eq1159 (τ X0)
       grind)
    | exact resolve eq1159 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq11319 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11293 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11293
    | (have j0 := eq11293 X0
       grind)
    | exact resolve eq11293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11293
  have eq11332 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11319 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11319
    | (have j0 := eq11319 X0
       grind)
    | exact resolve eq11319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11319
  have eq12468 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq142 x y X0
       grind)
    | exact superpose eq142 eq14
    | (have j1 := eq142 X0 y X0
       grind)
    | exact resolve eq14 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq197594 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12468 X0
       have i₂ := eq2929 x y
       grind)
    | exact superpose eq2929 eq12468
    | (have j0 := eq12468 X0
       have j1 := eq2929 X0 y
       grind)
    | (have r₁ := eq12468 X0
       have r₂ := eq2929 x y
       grind)
    | exact resolve eq12468 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929 eq12468
  have eq197596 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq197594 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197594
  have eq200521 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2004 (σ y) X0
       have i₂ := eq197596 (σ y)
       grind)
    | exact superpose eq197596 eq2004
    | (have j0 := eq2004 (σ y) X0
       grind)
    | exact resolve eq2004 eq197596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004 eq197596
  have eq200558 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq200521 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200521
  have eq200574 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq200558 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq200558
    | exact resolve eq200558 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200558
  have eq200585 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq200574 X0
       have j1 := eq11 X0 y
       grind)
    | (have r₁ := eq200574 X0
       have r₂ := eq11 X0 y
       grind)
    | exact resolve eq200574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200574
  have eq203868 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1159 y
       have i₂ := eq200585 y
       grind)
    | exact superpose eq200585 eq1159
    | (have j0 := eq1159 y
       grind)
    | exact resolve eq1159 eq200585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq203872 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11332 y
       have i₂ := eq200585 y
       grind)
    | exact superpose eq200585 eq11332
    | (have j0 := eq11332 y
       grind)
    | (have r₁ := eq11332 y
       have r₂ := eq200585 y
       grind)
    | exact resolve eq11332 eq200585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11332 eq200585
  have eq203929 : y = (M.op y y) := by grind
  clear eq203872
  have eq203933 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq203868
  have eq207183 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq8 y y x
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq8
    | exact resolve eq8 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207247 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1 y y
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq351
    | exact resolve eq351 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207370 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = y := by
    intro X0 X1
    first
    | (have i₁ := eq207247 X0 X1
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq207247
    | exact resolve eq207247 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207247
  have eq207381 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq207183 X0
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq207183
    | exact resolve eq207183 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203929 eq207183
  have eq232467 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1 (σ y) (σ y)
       have i₂ := eq203933
       grind)
    | exact superpose eq203933 eq351
    | exact resolve eq351 eq203933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq232560 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq232467 X0 X1
       have i₂ := eq203933
       grind)
    | exact superpose eq203933 eq232467
    | exact resolve eq232467 eq203933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203933 eq232467
  have eq232697 : y = (σ y) := by
    first
    | (have i₁ := eq232560 x x
       have i₂ := eq207370 x x
       grind)
    | exact superpose eq207370 eq232560
    | exact resolve eq232560 eq207370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207370 eq232560
  have eq233940 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq232697
       grind)
    | exact superpose eq232697 eq14
    | exact resolve eq14 eq232697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233994 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq233940
       have i₂ := eq207381 (σ x)
       grind)
    | exact superpose eq207381 eq233940
    | exact resolve eq233940 eq207381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233940
  have eq234001 : y ≠ (σ y) := by
    first
    | (have i₁ := eq233994
       have i₂ := eq207381 x
       grind)
    | exact superpose eq207381 eq233994
    | exact resolve eq233994 eq207381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207381 eq233994
  have eq234002 : False := by grind
  exact eq234002

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_x_pyx_Equation434 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law434 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq8 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X0) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq64 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X1) X0
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 X1 X0
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq24 X0 X0
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq47
    | exact resolve eq47 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq47 X1 (τ X0)
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 X1 (τ X0)
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq499 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) (σ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq21
    | (have j1 := eq45 X1 X0
       grind)
    | exact resolve eq21 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq961 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1217 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq99
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1270 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1217 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1217
    | (have j0 := eq1217 X0 X1
       grind)
    | exact resolve eq1217 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1665 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq95 y x
       grind)
    | exact superpose eq95 eq14
    | (have j1 := eq95 y x
       grind)
    | exact resolve eq14 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq4719 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq540 (τ X0) (τ X1)
       have i₂ := eq145 X0 X1
       grind)
    | exact superpose eq145 eq540
    | exact resolve eq540 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq4773 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4719 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4719
    | (have j0 := eq4719 X0 X1
       grind)
    | exact resolve eq4719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4782 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4773 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4773
    | (have j0 := eq4773 X0 X1
       grind)
    | exact resolve eq4773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4773
  have eq4786 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4782 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4782
    | (have j0 := eq4782 X0 X1
       grind)
    | exact resolve eq4782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4782
  have eq4787 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4786 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4786
    | (have j0 := eq4786 X0 X1
       grind)
    | exact resolve eq4786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4786
  have eq4788 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4787 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4787
    | (have j0 := eq4787 X0 X1
       grind)
    | exact resolve eq4787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4787
  have eq4808 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4788 (M.op X0 X0) X1
       have i₂ := eq64 (M.op X0 X0) X0
       grind)
    | exact superpose eq64 eq4788
    | (have j0 := eq4788 (M.op X0 X0) X1
       grind)
    | exact resolve eq4788 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq4848 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq4808 X0 X1
       have j1 := eq47 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq4808 X0 X1
       have r₂ := eq47 (M.op X0 X0) X1
       grind)
    | exact resolve eq4808 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4808
  have eq4865 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4848 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq4848
    | exact resolve eq4848 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4848
  have eq4887 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq499 X0 (M.op X0 X0)
       have i₂ := eq961 X0
       grind)
    | exact superpose eq961 eq499
    | (have j0 := eq499 X0 (M.op X0 X0)
       grind)
    | exact resolve eq499 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4913 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq499 (τ X0) (τ X1)
       have i₂ := eq145 X1 X0
       grind)
    | exact superpose eq145 eq499
    | (have j0 := eq499 (τ X0) (τ X1)
       grind)
    | exact resolve eq499 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4968 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4913 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4913
    | (have j0 := eq4913 X0 X1
       grind)
    | exact resolve eq4913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4913
  have eq4977 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4968 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4968
    | (have j0 := eq4968 X0 X1
       grind)
    | exact resolve eq4968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4968
  have eq4978 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4977 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4977
    | (have j0 := eq4977 X0 X1
       grind)
    | exact resolve eq4977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4977
  have eq4979 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4978 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4978
    | (have j0 := eq4978 X0 X1
       grind)
    | exact resolve eq4978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4978
  have eq5033 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1)
       have i₂ := eq4865 X1 (τ X0)
       grind)
    | exact superpose eq4865 eq16
    | exact resolve eq16 eq4865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq4865
  have eq5036 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5033 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5033
    | exact resolve eq5033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5033
  have eq5053 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq539 (M.op X0 X0) X0
       have i₂ := eq961 X0
       grind)
    | exact superpose eq961 eq539
    | (have j0 := eq539 (M.op X0 X0) X0
       grind)
    | exact resolve eq539 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5077 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq539 (τ X1) (τ X0)
       have i₂ := eq145 X1 X0
       grind)
    | exact superpose eq145 eq539
    | (have j0 := eq539 (τ X1) (τ X0)
       grind)
    | exact resolve eq539 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq539
  have eq5127 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5077 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5077
    | (have j0 := eq5077 X0 X1
       grind)
    | exact resolve eq5077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5077
  have eq5133 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5053 X0
       have j1 := eq4887 X0
       grind)
    | (have r₁ := eq5053 X0
       have r₂ := eq4887 X0
       grind)
    | exact resolve eq5053 eq4887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4887 eq5053
  have eq5139 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5127 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5127
    | (have j0 := eq5127 X0 X1
       grind)
    | exact resolve eq5127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5127
  have eq5142 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5139 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5139
    | (have j0 := eq5139 X0 X1
       grind)
    | exact resolve eq5139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5139
  have eq5144 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5142 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5142
    | (have j0 := eq5142 X0 X1
       grind)
    | exact resolve eq5142 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5142
  have eq5196 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ (M.op X1 X1)) X0
       have i₂ := eq5036 X0 X1
       grind)
    | exact superpose eq5036 eq47
    | exact resolve eq47 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq5203 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) ≠ X0 ∨ (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4788 (σ (M.op X1 X1)) X0
       have i₂ := eq5036 X0 X1
       grind)
    | exact superpose eq5036 eq4788
    | (have r₁ := eq4788 (σ (M.op X1 X1)) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))
       have r₂ := eq5036 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X1
       grind)
    | exact resolve eq4788 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4788
  have eq5204 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq961 (σ (M.op X0 X0))
       have i₂ := eq5036 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) X0
       grind)
    | exact superpose eq5036 eq961
    | exact resolve eq961 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq5221 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ X0 ∨ (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5203 X0 X1
       have i₂ := eq5204 X1
       grind)
    | exact superpose eq5204 eq5203
    | (have j0 := eq5203 X0 X1
       grind)
    | (have r₁ := eq5203 (σ (M.op X0 X0)) X0
       have r₂ := eq5204 X0
       grind)
    | exact resolve eq5203 eq5204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5203 eq5204
  have eq5242 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5221 X0 X1
       have j1 := eq5196 X0 X1
       grind)
    | (have r₁ := eq5221 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X1
       have r₂ := eq5196 (σ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq5221 X0 X1
       have r₂ := eq5196 X0 X1
       grind)
    | (have r₁ := eq5221 (σ (M.op X1 X1)) X1
       have r₂ := eq5196 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq5221 eq5196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5196 eq5221
  have eq5669 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ (M.op X1 X1)) X0
       have i₂ := eq5242 X0 X1
       grind)
    | exact superpose eq5242 eq21
    | exact resolve eq21 eq5242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq5242
  have eq15332 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5669 (σ X0) X0
       have i₂ := eq5133 X0
       grind)
    | exact superpose eq5133 eq5669
    | exact resolve eq5669 eq5133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5133 eq5669
  have eq35620 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1665
       have i₂ := eq1270 x y
       grind)
    | exact superpose eq1270 eq1665
    | (have j1 := eq1270 x y
       grind)
    | (have r₁ := eq1665
       have r₂ := eq1270 x y
       grind)
    | exact resolve eq1665 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270 eq1665
  have eq35621 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq35620
  have eq35627 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq35621
       grind)
    | exact superpose eq35621 eq9
    | exact resolve eq9 eq35621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35621
  have eq35728 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq35627
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq35627
    | exact resolve eq35627 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35627
  have eq35733 : y = (k y x) := by
    first
    | (have j1 := eq100 y x
       grind)
    | (have r₁ := eq35728
       have r₂ := eq100 y x
       grind)
    | exact resolve eq35728 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq35728
  have eq36813 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq499 y x
       have i₂ := eq35733
       grind)
    | exact superpose eq35733 eq499
    | (have j0 := eq499 y x
       grind)
    | exact resolve eq499 eq35733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq36816 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4979 y x
       have i₂ := eq35733
       grind)
    | exact superpose eq35733 eq4979
    | (have j0 := eq4979 y x
       grind)
    | exact resolve eq4979 eq35733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4979
  have eq36817 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq5144 y x
       have i₂ := eq35733
       grind)
    | exact superpose eq35733 eq5144
    | (have j0 := eq5144 y x
       grind)
    | exact resolve eq5144 eq35733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5144
  have eq36818 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq36816
       have r₂ := eq36817
       grind)
    | exact resolve eq36816 eq36817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36816 eq36817
  have eq36819 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq36813
       have i₂ := eq15332 y
       grind)
    | exact superpose eq15332 eq36813
    | exact resolve eq36813 eq15332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36813
  have eq36820 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq36819
       have i₂ := eq36818
       grind)
    | exact superpose eq36818 eq36819
    | exact resolve eq36819 eq36818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36819
  have eq36821 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36820
       have i₂ := eq15332 y
       grind)
    | exact superpose eq15332 eq36820
    | exact resolve eq36820 eq15332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36820
  have eq36822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36821
       have i₂ := eq36818
       grind)
    | exact superpose eq36818 eq36821
    | exact resolve eq36821 eq36818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36821
  have eq36823 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq36822
       have r₂ := eq14
       grind)
    | exact resolve eq36822 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36822
  have eq37067 : ∀ X0 : G, (k (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5036 X0 y
       have i₂ := eq36818
       grind)
    | exact superpose eq36818 eq5036
    | exact resolve eq5036 eq36818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5036 eq36818
  have eq37180 : ∀ X0 : G, (k (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37067 X0
       have i₂ := eq36823
       grind)
    | exact superpose eq36823 eq37067
    | exact resolve eq37067 eq36823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36823 eq37067
  have eq37591 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (σ y) X0
       have i₂ := eq37180 (σ X0)
       grind)
    | exact superpose eq37180 eq20
    | exact resolve eq20 eq37180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37180
  have eq37625 : ∀ X0 : G, (τ (σ X0)) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq37591 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq37591
    | exact resolve eq37591 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37591
  have eq37651 : ∀ X0 : G, (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37625 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37625
    | exact resolve eq37625 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37625
  have eq37898 : x = y := by
    first
    | (have i₁ := eq35733
       have i₂ := eq37651 x
       grind)
    | exact superpose eq37651 eq35733
    | exact resolve eq35733 eq37651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35733 eq37651
  have eq38622 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq37898
       grind)
    | exact superpose eq37898 eq14
    | exact resolve eq14 eq37898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37898
  have eq38631 : False := by grind
  exact eq38631

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pyy_pyx_Equation434 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law434 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq56 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq16
  have eq102 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq218 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq42 X2 X0
       grind)
    | exact superpose eq42 eq22
    | (have j1 := eq42 X2 X0
       grind)
    | exact resolve eq22 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq257 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 X1) X0
       have i₂ := eq34 X1 (σ X0)
       grind)
    | exact superpose eq34 eq20
    | exact resolve eq20 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) ≠ (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X1 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq102
    | exact resolve eq102 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq575 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq102 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq579 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq560 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq612 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq575 (σ X0)
       grind)
    | exact superpose eq575 eq13
    | exact resolve eq13 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq612 X0
       have i₂ := eq575 X0
       grind)
    | exact superpose eq575 eq612
    | exact resolve eq612 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq755 : ∀ X0 X1 : G, (τ (k (M.op X0 X0) (σ X1))) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X1)
       have i₂ := eq579 X0 (σ X1)
       grind)
    | exact superpose eq579 eq61
    | exact resolve eq61 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq579
  have eq761 : ∀ X0 X1 : G, (k X1 X1) = (τ (k (M.op X0 X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq755 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq755
    | exact resolve eq755 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq781 : ∀ X0 X1 : G, (k X1 X1) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq761 X0 X1
       have i₂ := eq20 (M.op X0 X0) X1
       grind)
    | exact superpose eq20 eq761
    | exact resolve eq761 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq761
  have eq1000 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1076 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1000 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1000
    | (have j0 := eq1000 X0 X1
       grind)
    | exact resolve eq1000 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1319 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq619 X0
       grind)
    | exact superpose eq619 eq22
    | exact resolve eq22 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq1893 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq218 y X0 x
       grind)
    | exact superpose eq218 eq14
    | (have j1 := eq218 y X0 x
       grind)
    | exact resolve eq14 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq34609 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1893 X0
       have i₂ := eq1076 x y
       grind)
    | exact superpose eq1076 eq1893
    | (have j0 := eq1893 X0
       have j1 := eq1076 X0 y
       grind)
    | (have r₁ := eq1893 X0
       have r₂ := eq1076 x y
       grind)
    | exact resolve eq1893 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq1893
  have eq34610 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq34609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34609
  have eq34723 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op X0 X0)) y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq257 y X0
       have i₂ := eq34610 (σ y)
       grind)
    | exact superpose eq34610 eq257
    | exact resolve eq257 eq34610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq34610
  have eq34744 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34723 x
       have i₂ := eq781 x y
       grind)
    | exact superpose eq781 eq34723
    | exact resolve eq34723 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq34723
  have eq34780 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34744
       have i₂ := eq575 y
       grind)
    | exact superpose eq575 eq34744
    | exact resolve eq34744 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq34744
  have eq34791 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34780
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq34780
    | exact resolve eq34780 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34780
  have eq34792 : y = (M.op y y) := by grind
  clear eq34791
  have eq34954 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq34792
       grind)
    | exact superpose eq34792 eq22
    | exact resolve eq22 eq34792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq35003 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1319 y X0
       have i₂ := eq34792
       grind)
    | exact superpose eq34792 eq1319
    | exact resolve eq1319 eq34792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319 eq34792
  have eq38866 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35003 (σ x)
       grind)
    | exact superpose eq35003 eq14
    | exact resolve eq14 eq35003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35003
  have eq38889 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq38866
       have i₂ := eq34954 x
       grind)
    | exact superpose eq34954 eq38866
    | exact resolve eq38866 eq34954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34954 eq38866
  have eq38890 : False := by grind
  exact eq38890

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxy_pyx_Equation434 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law434 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq8 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X0)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq11
    | (have r₁ := eq11 X0 (M.op X1 X0)
       have r₂ := eq21 X0 X1
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq37 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 X1 (M.op X0 X0)
       have r₂ := eq22 X0 X1
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X1) X0
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq45 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (M.op X1 X1) X0
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq30
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq62 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op X1 X1)
       have i₂ := eq39 (τ X0) X1
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq64 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62
    | exact resolve eq62 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq80 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq41 X0 X0
       grind)
    | exact superpose eq41 eq22
    | (have j1 := eq41 X0 X0
       grind)
    | exact resolve eq22 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) (σ X1)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq21
    | (have j1 := eq41 (k X0 X1) X0
       grind)
    | exact resolve eq21 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq11
    | (have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq11 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq132 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq158 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (k X0 (τ X1)) X2
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq57
    | exact resolve eq57 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 (M.op X1 (σ X0))
       have i₂ := eq30 (σ X0) X1
       grind)
    | exact superpose eq30 eq57
    | exact resolve eq57 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq161
    | exact resolve eq161 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq319 : ∀ X0 X1 : G, (k X0 (τ (σ (k X0 X1)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq173 X0 (σ X1)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq173
    | (have j1 := eq41 X1 X0
       grind)
    | exact resolve eq173 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq173
  have eq331 : ∀ X0 X1 : G, (k X0 (k X0 X1)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq319 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq319
    | (have j0 := eq319 X0 X1
       grind)
    | exact resolve eq319 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq456 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op (τ X1) X0) X2
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq57
    | (have j1 := eq52 X1 X0
       grind)
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq57
  have eq483 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq158 X0 X1 X2
       grind)
    | exact superpose eq158 eq481
    | (have j0 := eq481 X0 X1 X2
       grind)
    | exact resolve eq481 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq481
  have eq494 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq456
    | (have j0 := eq456 X0 X1
       grind)
    | exact resolve eq456 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq532 : ∀ X0 X1 : G, (M.op X1 (k (σ (τ X0)) X0)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq80
    | (have j0 := eq80 (τ X0) X1
       grind)
    | exact resolve eq80 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq80
  have eq554 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq559 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq554
    | (have j0 := eq554 X0 X1
       grind)
    | exact resolve eq554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq667 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq14
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq14 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq699 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq667 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq667
    | (have j0 := eq667 X0 X1
       grind)
    | exact resolve eq667 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq701 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq699
  have eq754 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (τ X0) (τ X1)
       have i₂ := eq132 X1 X0
       grind)
    | exact superpose eq132 eq84
    | (have j0 := eq84 (τ X0) (τ (k X0 X1))
       grind)
    | exact resolve eq84 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq774 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq754 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq754
    | (have j0 := eq754 X0 X1
       grind)
    | exact resolve eq754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq781 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq774
    | (have j0 := eq774 X0 X1
       grind)
    | exact resolve eq774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq782 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq781 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq781
    | (have j0 := eq781 X0 X1
       grind)
    | exact resolve eq781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq783 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq782 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq782
    | (have j0 := eq782 X0 X1
       grind)
    | exact resolve eq782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq1676 : ∀ X0 X1 : G, (k X1 X1) = (k (k X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 (k X1 X1) X0
       have i₂ := eq559 X1 X0
       grind)
    | exact superpose eq559 eq30
    | (have j1 := eq559 X1 X1
       grind)
    | exact resolve eq30 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq559
  have eq1839 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq783 X0 (σ (M.op X1 X1))
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq783
    | (have j0 := eq783 X0 X0
       grind)
    | exact resolve eq783 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq3128 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq701
    | exact resolve eq701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq3297 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3128 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3128
  have eq3829 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq674
       have i₂ := eq494 x y
       grind)
    | exact superpose eq494 eq674
    | (have j1 := eq494 x y
       grind)
    | (have r₁ := eq674
       have r₂ := eq494 x y
       grind)
    | exact resolve eq674 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq674
  have eq3830 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq3829
  have eq4072 : (M.op x y) = (τ (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq3830
       grind)
    | exact superpose eq3830 eq9
    | exact resolve eq9 eq3830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3830
  have eq4123 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4072
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4072
    | exact resolve eq4072 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4072
  have eq4235 : y ≠ y ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq4123
       grind)
    | exact superpose eq4123 eq11
    | (have r₁ := eq11 y x
       have r₂ := eq4123
       grind)
    | exact resolve eq11 eq4123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4123
  have eq4237 : y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq4235
  have eq4238 : y = (k y x) := by
    first
    | (have j1 := eq3297 y x
       grind)
    | (have r₁ := eq4237
       have r₂ := eq3297 y x
       grind)
    | exact resolve eq4237 eq3297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3297 eq4237
  have eq4339 : y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq783 y x
       have i₂ := eq4238
       grind)
    | exact superpose eq4238 eq783
    | (have j0 := eq783 y y
       grind)
    | exact resolve eq783 eq4238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq4745 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq38 X0 y
       have i₂ := eq4339
       grind)
    | exact superpose eq4339 eq38
    | exact resolve eq38 eq4339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4339
  have eq5287 : y ≠ y ∨ y = (M.op y x) := by
    first
    | (have j0 := eq4745 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4745
  have eq5288 : y = (M.op y x) := by grind
  clear eq5287
  have eq5339 : x = (M.op x y) := by
    first
    | (have i₁ := eq21 x y
       have i₂ := eq5288
       grind)
    | exact superpose eq5288 eq21
    | exact resolve eq21 eq5288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5288
  have eq17412 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op X0 (σ (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq1839 X0 X1
       grind)
    | exact superpose eq1839 eq38
    | (have j1 := eq1839 X0 X2
       grind)
    | exact resolve eq38 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1839
  have eq20695 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17412 X0 (σ (M.op X1 X1)) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17412
  have eq20696 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq20695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20695
  have eq44944 : ∀ X0 X1 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq483 (τ X0) X0 X1
       have i₂ := eq1676 (τ X1) (τ X0)
       grind)
    | exact superpose eq1676 eq483
    | (have j0 := eq483 (τ X0) X0 x
       have j1 := eq1676 X0 (τ X0)
       grind)
    | exact resolve eq483 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq1676
  have eq45051 : ∀ X0 X1 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq44944 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44944
  have eq45068 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq45051 X0 x
       have i₂ := eq45 (τ x) (τ X0)
       grind)
    | exact superpose eq45 eq45051
    | (have j0 := eq45051 X0 x
       grind)
    | exact resolve eq45051 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq45051
  have eq45096 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq45068 X0
       have j1 := eq11 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq45068 X0
       have r₂ := eq11 (τ X0) (τ X0)
       grind)
    | exact resolve eq45068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45068
  have eq45122 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45096 X0
       have i₂ := eq132 X0 X0
       grind)
    | exact superpose eq132 eq45096
    | exact resolve eq45096 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq45096
  have eq45518 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq45122 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45122
    | exact resolve eq45122 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45122
  have eq45721 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq45518 X0
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq45518
    | exact resolve eq45518 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq45518
  have eq45746 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq45721 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45721
    | exact resolve eq45721 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45721
  have eq176752 : y = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq331 y x
       have i₂ := eq4238
       grind)
    | exact superpose eq4238 eq331
    | (have j0 := eq331 y x
       grind)
    | exact resolve eq331 eq4238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq4238
  have eq177183 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq176752
       have i₂ := eq45746 y
       grind)
    | exact superpose eq45746 eq176752
    | exact resolve eq176752 eq45746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45746 eq176752
  have eq177512 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21 (σ x) (σ y)
       have i₂ := eq177183
       grind)
    | exact superpose eq177183 eq21
    | exact resolve eq21 eq177183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq177183
  have eq178078 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq177512
       grind)
    | exact superpose eq177512 eq14
    | exact resolve eq14 eq177512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177512
  have eq178118 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq178078
       have i₂ := eq5339
       grind)
    | exact superpose eq5339 eq178078
    | exact resolve eq178078 eq5339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5339 eq178078
  have eq178119 : y = (M.op y y) := by grind
  clear eq178118
  have eq179122 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq178119
       grind)
    | exact superpose eq178119 eq22
    | exact resolve eq22 eq178119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq179168 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq20696 X0 y
       have i₂ := eq178119
       grind)
    | exact superpose eq178119 eq20696
    | exact resolve eq20696 eq178119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20696 eq178119
  have eq187557 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq179168 (σ x)
       grind)
    | exact superpose eq179168 eq14
    | exact resolve eq14 eq179168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179168
  have eq187631 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq187557
       have i₂ := eq179122 x
       grind)
    | exact superpose eq179122 eq187557
    | exact resolve eq187557 eq179122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179122 eq187557
  have eq187632 : False := by grind
  exact eq187632
