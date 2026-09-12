import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq288 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq288 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq288 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq288 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq300 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq289 (σ X0)
       grind)
    | exact superpose eq289 eq15
    | exact resolve eq15 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq289 (τ X0)
       grind)
    | exact superpose eq289 eq31
    | exact resolve eq31 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq313 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq306 X0
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq306
    | exact resolve eq306 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq300
    | exact resolve eq300 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq300
  have eq800 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq800 X0 X1
       have i₂ := eq319 X0
       grind)
    | exact superpose eq319 eq800
    | (have j0 := eq800 X0 X1
       grind)
    | exact resolve eq800 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq4725 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq817 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq817
    | exact resolve eq817 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq4837 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4725 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq4725
    | (have j0 := eq4725 X0 X1
       grind)
    | exact resolve eq4725 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4725
  have eq4840 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4837 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq4837 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq4837 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4837
  have eq4841 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4840 X0 X1
       have i₂ := eq313 X0
       grind)
    | exact superpose eq313 eq4840
    | (have j0 := eq4840 X0 X1
       grind)
    | exact resolve eq4840 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq4840
  have eq4842 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4841 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4841
    | (have j0 := eq4841 X0 X1
       grind)
    | exact resolve eq4841 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4841
  have eq4843 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4842 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4842
    | exact resolve eq4842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4849 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4842 (σ X0) X1
       grind)
    | exact superpose eq4842 eq15
    | (have j1 := eq4842 (σ X0) X1
       grind)
    | exact resolve eq15 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4842
  have eq4873 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4849 X0 X1
       have i₂ := eq319 X0
       grind)
    | exact superpose eq319 eq4849
    | (have j0 := eq4849 X0 X1
       grind)
    | exact resolve eq4849 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4849
  have eq4902 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq4843 (τ X1) X0
       grind)
    | exact superpose eq4843 eq17
    | (have j1 := eq4843 (τ X1) X0
       grind)
    | exact resolve eq17 eq4843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4843
  have eq5029 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4902 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4902
    | exact resolve eq4902 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4902
  have eq5079 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5029 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5029
    | (have j0 := eq5029 X0 X1
       grind)
    | exact resolve eq5029 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5029
  have eq11920 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4873 x y
       grind)
    | exact superpose eq4873 eq16
    | (have j1 := eq4873 x y
       grind)
    | exact resolve eq16 eq4873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12068 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4873 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4873
  have eq12100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11920
       have i₂ := eq5079 y x
       grind)
    | exact superpose eq5079 eq11920
    | (have j1 := eq5079 y x
       grind)
    | (have r₁ := eq11920
       have r₂ := eq5079 y x
       grind)
    | exact resolve eq11920 eq5079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11920
  have eq12101 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12100
  have eq12105 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq12101
       grind)
    | exact superpose eq12101 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq12101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12106 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq12101
       grind)
    | exact superpose eq12101 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq12101
       grind)
    | exact resolve eq13 eq12101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12101
  have eq12131 : x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12106
  have eq12132 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq12105
       have r₂ := eq12131
       grind)
    | exact resolve eq12105 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12105 eq12131
  have eq12158 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12068 x y
       have i₂ := eq12132
       grind)
    | exact superpose eq12132 eq12068
    | (have j0 := eq12068 x y
       grind)
    | exact resolve eq12068 eq12132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12068 eq12132
  have eq12198 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12158
  have eq12199 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12198
  have eq12462 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12199
       grind)
    | exact superpose eq12199 eq16
    | exact resolve eq16 eq12199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12465 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq12199
       grind)
    | exact superpose eq12199 eq12
    | exact resolve eq12 eq12199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12466 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq12199
       grind)
    | exact superpose eq12199 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq12199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12199
  have eq12492 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq12466
       have r₂ := eq319 x
       grind)
    | exact resolve eq12466 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12466
  have eq12493 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12465
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12465
    | exact resolve eq12465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12465
  have eq12495 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12492
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12492
    | exact resolve eq12492 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12492
  have eq12496 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12495
       have i₂ := eq319 x
       grind)
    | exact superpose eq319 eq12495
    | exact resolve eq12495 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq12495
  have eq12497 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq12496
       have r₂ := eq12493
       grind)
    | exact resolve eq12496 eq12493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12493 eq12496
  have eq12505 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5079 y x
       have i₂ := eq12497
       grind)
    | exact superpose eq12497 eq5079
    | (have j0 := eq5079 y x
       grind)
    | exact resolve eq5079 eq12497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5079 eq12497
  have eq12567 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq12505
       have r₂ := eq12462
       grind)
    | exact resolve eq12505 eq12462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12505
  have eq12584 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12462
       have i₂ := eq12567
       grind)
    | exact superpose eq12567 eq12462
    | exact resolve eq12462 eq12567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12462 eq12567
  have eq12613 : False := by grind
  exact eq12613

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq376 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq87 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq379 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq376 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq380 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq382 X0 X1
       have j1 := eq378 X0 X1
       grind)
    | (have r₁ := eq382 X0 X1
       have r₂ := eq378 X0 X1
       grind)
    | (have r₁ := eq382 (k X0 X1) X0
       have r₂ := eq378 X0 X1
       grind)
    | (have r₁ := eq382 X0 X0
       have r₂ := eq378 X0 X0
       grind)
    | exact resolve eq382 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq382
  have eq535 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq386
    | exact resolve eq386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq386 x y
       grind)
    | exact superpose eq386 eq16
    | (have j1 := eq386 x y
       grind)
    | exact resolve eq16 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq560 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq535
    | (have j0 := eq535 X0 X1
       grind)
    | exact resolve eq535 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq535
  have eq613 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq560
    | exact resolve eq560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq696 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq613 (τ X0) X1
       grind)
    | exact superpose eq613 eq18
    | (have j1 := eq613 (τ X0) X1
       grind)
    | exact resolve eq18 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq613
  have eq885 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq696 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq696
    | exact resolve eq696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq937 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq885 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq885
    | (have j0 := eq885 X0 X1
       grind)
    | exact resolve eq885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq997 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq542
       have i₂ := eq937 x y
       grind)
    | exact superpose eq937 eq542
    | (have j1 := eq937 (σ x) (σ y)
       grind)
    | (have r₁ := eq542
       have r₂ := eq937 x y
       grind)
    | exact resolve eq542 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq997
  have eq1003 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq998
  have eq1055 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq542
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq542
    | exact resolve eq542 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq1003
  have eq1056 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1055
  have eq1057 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1056
  have eq1068 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1057
  have eq1080 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1068
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1068
    | exact resolve eq1068 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1174 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1080
       grind)
    | exact superpose eq1080 eq16
    | exact resolve eq16 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq1222 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1174
       have i₂ := eq937 x y
       grind)
    | exact superpose eq937 eq1174
    | (have j1 := eq937 x y
       grind)
    | (have r₁ := eq1174
       have r₂ := eq937 x y
       grind)
    | exact resolve eq1174 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq1223 : x = (M.op y y) := by grind
  clear eq1222
  have eq1229 : (M.op x y) = (k x y) := by grind
  clear eq1223
  have eq1283 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1174
       have i₂ := eq1229
       grind)
    | exact superpose eq1229 eq1174
    | exact resolve eq1174 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq1229
  have eq1286 : False := by grind
  exact eq1286

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pyy_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq66 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq184 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq209 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq239 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq288 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq239 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq289 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq288 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq323 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq289 (σ X0)
       grind)
    | exact superpose eq289 eq15
    | exact resolve eq15 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq289 (τ X0)
       grind)
    | exact superpose eq289 eq33
    | exact resolve eq33 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq330 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq327 X0
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq327
    | exact resolve eq327 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq334 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq323
    | exact resolve eq323 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq323
  have eq369 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq330 X0
       grind)
    | exact superpose eq330 eq9
    | exact resolve eq9 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq209 (σ X0) X1
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq209
    | (have j0 := eq209 (σ X0) X1
       grind)
    | exact resolve eq209 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (σ X0)
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq9
    | exact resolve eq9 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1329 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq385 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq385 X0 (σ X0)
       grind)
    | exact superpose eq385 eq10
    | (have j1 := eq385 X1 X0
       grind)
    | exact resolve eq10 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq2199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1329 (σ X1) X0
       grind)
    | exact superpose eq1329 eq15
    | (have j1 := eq1329 (σ X1) X0
       grind)
    | exact resolve eq15 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq2224 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2199 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2199
    | (have j0 := eq2199 X0 X1
       grind)
    | exact resolve eq2199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq3692 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2224 x y
       grind)
    | exact superpose eq2224 eq16
    | (have j1 := eq2224 x y
       grind)
    | exact resolve eq16 eq2224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq3908 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3692
       have i₂ := eq209 x y
       grind)
    | exact superpose eq209 eq3692
    | (have j1 := eq209 x y
       grind)
    | exact resolve eq3692 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3692
  have eq3914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq3908
  have eq3915 : y = (M.op x x) := by grind
  clear eq3914
  have eq3916 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq3915
       grind)
    | exact superpose eq3915 eq9
    | exact resolve eq9 eq3915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3919 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq369 X0 x
       have i₂ := eq3915
       grind)
    | exact superpose eq3915 eq369
    | exact resolve eq369 eq3915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq3926 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (σ y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq389 x X0 X1
       have i₂ := eq3915
       grind)
    | exact superpose eq3915 eq389
    | exact resolve eq389 eq3915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3915
  have eq3992 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 (M.op X1 y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 y) X0 y
       have i₂ := eq3916 X1 y
       grind)
    | exact superpose eq3916 eq9
    | exact resolve eq9 eq3916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq4450 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq3926 X0 (σ y)
       have i₂ := eq334 y
       grind)
    | exact superpose eq334 eq3926
    | exact resolve eq3926 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3926
  have eq15313 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) ∨ (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0
       have i₂ := eq209 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq66 X0
       have i₂ := eq209 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq209 eq66
    | (have j1 := eq209 (M.op X1 X1) X0
       grind)
    | exact resolve eq66 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq209
  have eq15322 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq15313 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15313
  have eq15501 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15322 X0 (σ X0)
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq15322
    | exact resolve eq15322 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq15503 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15322 X0 (τ X0)
       have i₂ := eq330 X0
       grind)
    | exact superpose eq330 eq15322
    | exact resolve eq15322 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq20849 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq15501 X0 (σ X1)
       grind)
    | exact superpose eq15501 eq15
    | exact resolve eq15 eq15501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15501
  have eq20885 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20849 X0 X1
       have i₂ := eq15322 X1 X0
       grind)
    | exact superpose eq15322 eq20849
    | exact resolve eq20849 eq15322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20849
  have eq20984 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ X1)) = (σ (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X0 X0) X1
       have i₂ := eq15503 X0 X1
       grind)
    | exact superpose eq15503 eq19
    | exact resolve eq19 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15503
  have eq21008 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20984 X0 X1
       have i₂ := eq15322 (σ X1) X0
       grind)
    | exact superpose eq15322 eq20984
    | exact resolve eq20984 eq15322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15322 eq20984
  have eq26751 : ∀ X0 : G, (σ y) = (M.op (σ (M.op (M.op X0 X0) y)) (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq4450 (σ (M.op X0 X0))
       have i₂ := eq20885 X0 y
       grind)
    | exact superpose eq20885 eq4450
    | exact resolve eq4450 eq20885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4450 eq20885
  have eq27481 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (σ (M.op (τ X0) y))) := by
    intro X0
    first
    | (have i₁ := eq21008 X0 (M.op (τ X0) y)
       have i₂ := eq3919 X0
       grind)
    | exact superpose eq3919 eq21008
    | exact resolve eq21008 eq3919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919 eq21008
  have eq27678 : ∀ X0 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq27481 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27481
    | exact resolve eq27481 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27481
  have eq43284 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 y)) (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq26751 (M.op X0 y)
       have i₂ := eq3992 (M.op X0 y) X0
       grind)
    | exact superpose eq3992 eq26751
    | exact resolve eq26751 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992 eq26751
  have eq43397 : ∀ X0 X1 : G, (σ (M.op X1 y)) = (M.op (M.op X0 (σ (M.op X1 y))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq389 y X0 (σ (M.op X1 y))
       have i₂ := eq43284 X1
       grind)
    | exact superpose eq43284 eq389
    | exact resolve eq389 eq43284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq43284
  have eq57862 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq43397 (M.op X0 X0) (τ X0)
       have i₂ := eq27678 X0
       grind)
    | exact superpose eq27678 eq43397
    | exact resolve eq43397 eq27678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27678 eq43397
  have eq58000 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq57862 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57862
    | exact resolve eq57862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57862
  have eq58294 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58000 x
       grind)
    | exact superpose eq58000 eq16
    | (have r₁ := eq16
       have r₂ := eq58000 x
       grind)
    | exact resolve eq16 eq58000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58000
  have eq58526 : False := by grind
  exact eq58526

/-- `Equation1488`: `x = (y ◇ x) ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1488 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1488 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1488.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq152 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq153 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq3650 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq4078 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq152 X1 X0
       grind)
    | exact superpose eq152 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq152 X1 X0
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq152 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq152 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq13 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq4091 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4078 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4078
  have eq4092 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = (k X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4091 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4091
  have eq4218 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4092 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4092
    | exact resolve eq4092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4092
  have eq4285 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4218 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4218
    | (have j0 := eq4218 X0 X1
       grind)
    | exact resolve eq4218 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4218
  have eq4334 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq4285 X1 X0
       grind)
    | exact superpose eq4285 eq10
    | (have j1 := eq4285 X1 X0
       grind)
    | exact resolve eq10 eq4285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4386 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4334 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq4334
    | (have j0 := eq4334 X0 X1
       grind)
    | exact resolve eq4334 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334
  have eq4443 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq4386 (σ X0) X1
       grind)
    | exact superpose eq4386 eq37
    | (have j1 := eq4386 (σ X0) X1
       grind)
    | exact resolve eq37 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4386
  have eq4719 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq4443 X1 (σ X0)
       grind)
    | exact superpose eq4443 eq28
    | (have j1 := eq4443 X1 (σ X0)
       grind)
    | exact resolve eq28 eq4443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4443
  have eq4781 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4719 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4719
    | (have j0 := eq4719 X0 X1
       grind)
    | exact resolve eq4719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4816 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4781 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4781
    | (have j0 := eq4781 X0 X1
       grind)
    | exact resolve eq4781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4781
  have eq4826 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4816 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4816
    | (have j0 := eq4816 X0 X1
       grind)
    | exact resolve eq4816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4816
  have eq4994 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4826 (τ X0) (τ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq4826
    | (have j0 := eq4826 (τ X0) (τ X1)
       grind)
    | exact resolve eq4826 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4826
  have eq5193 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4994 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4994
    | (have j0 := eq4994 X0 X1
       grind)
    | exact resolve eq4994 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994
  have eq5269 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5193 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5193
    | (have j0 := eq5193 X0 X1
       grind)
    | exact resolve eq5193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5193
  have eq5329 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5269 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5269
    | (have j0 := eq5269 X0 X1
       grind)
    | exact resolve eq5269 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5269
  have eq5387 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5329 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5329
    | (have j0 := eq5329 X0 X1
       grind)
    | exact resolve eq5329 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5329
  have eq5476 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq5387 X0 X1
       grind)
    | exact superpose eq5387 eq11
    | (have j1 := eq5387 X0 X1
       grind)
    | exact resolve eq11 eq5387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5387
  have eq5602 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5476 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq5476
    | (have j0 := eq5476 X0 X1
       grind)
    | exact resolve eq5476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476
  have eq5682 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5602 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5602
    | (have j0 := eq5602 (τ (σ (k X0 X1))) (τ (σ X1))
       grind)
    | exact resolve eq5602 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5602
  have eq5856 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5682 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5682
    | (have j0 := eq5682 X0 X1
       grind)
    | exact resolve eq5682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5682
  have eq5861 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5856 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5856
    | (have j0 := eq5856 X0 X1
       grind)
    | exact resolve eq5856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5856
  have eq6388 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5861 x y
       grind)
    | exact superpose eq5861 eq16
    | (have j1 := eq5861 x y
       grind)
    | exact resolve eq16 eq5861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5861
  have eq6425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6388
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq6388
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq6388
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6388
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6426 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq6388
       have i₂ := eq4285 y x
       grind)
    | exact superpose eq4285 eq6388
    | (have j1 := eq4285 y x
       grind)
    | (have r₁ := eq6388
       have r₂ := eq4285 y x
       grind)
    | (have r₁ := eq6388
       have r₂ := eq4285 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6388
       have r₂ := eq4285 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6388 eq4285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285 eq6388
  have eq6429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by grind
  clear eq6426
  have eq6430 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq6429
  have eq6431 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6425
  have eq6432 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6431
  have eq6435 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6430
       grind)
    | exact superpose eq6430 eq16
    | exact resolve eq16 eq6430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6430
  have eq6436 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6435
       have r₂ := eq22 x
       grind)
    | exact resolve eq6435 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6435
  have eq6442 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3650 x y
       have i₂ := eq6436
       grind)
    | exact superpose eq6436 eq3650
    | (have j0 := eq3650 x y
       grind)
    | exact resolve eq3650 eq6436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3650 eq6436
  have eq6447 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6442
  have eq6448 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6447
  have eq6462 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6448
       grind)
    | exact superpose eq6448 eq16
    | exact resolve eq16 eq6448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6448
  have eq6482 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6462
       have i₂ := eq6432
       grind)
    | exact superpose eq6432 eq6462
    | exact resolve eq6462 eq6432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6432 eq6462
  have eq6483 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6482
  have eq6484 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq6483
  have eq6485 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6484
       grind)
    | exact superpose eq6484 eq16
    | exact resolve eq16 eq6484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6484
  have eq6486 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq6485
       have r₂ := eq22 x
       grind)
    | exact resolve eq6485 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6485
  have eq6487 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6486
       grind)
    | exact superpose eq6486 eq16
    | exact resolve eq16 eq6486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6488 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6486
       grind)
    | exact superpose eq6486 eq10
    | exact resolve eq10 eq6486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6486
  have eq6545 : x = y := by
    first
    | (have i₁ := eq6488
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6488
    | exact resolve eq6488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6488
  have eq6546 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6487
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6487
    | exact resolve eq6487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6487
  have eq6547 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6546
       have i₂ := eq6545
       grind)
    | exact superpose eq6545 eq6546
    | exact resolve eq6546 eq6545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6545 eq6546
  have eq6548 : False := by grind
  exact eq6548

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_y_pyy_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  clear eq36
  have eq51 : x ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq104 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X0 X0) (k X0 (M.op X0 X0)))) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    grind
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq113 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq107
  have eq172 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq112
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq112 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq172
  have eq231 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq61 eq63
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq63 X0 X2
       grind)
    | exact superpose eq63 eq14
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X1 X2
       have i₂ := eq59 X2 X3 X0
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq59 y X1 X0
       grind)
    | exact superpose eq59 eq57
    | exact resolve eq57 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq59 sF3 x x
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = (M.op (M.op X2 (k X0 (M.op X0 X0))) (M.op (M.op X1 (M.op (M.op X0 X0) X1)) X1)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq514 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq60 eq62
    | exact resolve eq62 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X0)) X0) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3)) X1 X2 X0
       have i₂ := eq59 X0 X2 X3
       grind)
    | exact superpose eq59 eq62
    | exact resolve eq62 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq62
    | exact resolve eq62 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0 x (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq63 (M.op (M.op X0 (M.op X0 X0)) X0) x
       grind)
    | exact superpose eq63 eq62
    | exact resolve eq62 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X0 (M.op X1 X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op (M.op X0 (M.op X1 X0)) X0) (M.op x (M.op x X1))
       have i₂ := eq62 X0 x x X1
       grind)
    | exact superpose eq62 eq63
    | exact resolve eq63 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq772 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq71 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq71 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq71 X0 X1
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq782 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq781 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq786 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq772
    | (have j0 := eq772 X0 X1
       grind)
    | exact resolve eq772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq858 : ∀ X0 : G, (M.op (M.op X0 X0) (k X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op (M.op X0 X0) (k X0 (M.op X0 X0))) (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 X0 X0 (M.op (M.op X0 X0) (k X0 (M.op X0 X0)))
       have i₂ := eq104 X0 X0
       grind)
    | exact superpose eq104 eq59
    | (have j1 := eq104 X0 x
       grind)
    | exact resolve eq59 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq1327 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq245 X0 x x
       grind)
    | exact superpose eq245 eq63
    | exact resolve eq63 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1330 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1327 X0
       have i₂ := eq245 X0 X0 X0
       grind)
    | exact superpose eq245 eq1327
    | exact resolve eq1327 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1473 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq247 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3720 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq514 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1330 sF0
       grind)
    | exact superpose eq1330 eq514
    | exact resolve eq514 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3743 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq3720
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq3720
    | exact resolve eq3720 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq3745 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3743 eq514
    | exact resolve eq514 eq3743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514 eq3743
  have eq3767 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3745 eq14
    | exact resolve eq14 eq3745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3745
  have eq3796 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq515 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1330 sF4
       grind)
    | exact superpose eq1330 eq515
    | exact resolve eq515 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3819 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3796
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3796
    | exact resolve eq3796 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3796
  have eq3836 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3819 eq515
    | exact resolve eq515 eq3819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819
  have eq3858 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3836 eq14
    | exact resolve eq14 eq3836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3915 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3767 eq57
    | exact resolve eq57 eq3767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3767
  have eq3977 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq782 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq782
    | (have j0 := eq782 (τ X0)
       grind)
    | exact resolve eq782 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq782
  have eq3985 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3977 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3977
    | (have j0 := eq3977 X0
       grind)
    | exact resolve eq3977 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3977
  have eq3991 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3985 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3985
    | (have j0 := eq3985 X0
       grind)
    | exact resolve eq3985 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3985
  have eq4054 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3858 eq58
    | exact resolve eq58 eq3858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4079 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4054 eq3836
    | exact resolve eq3836 eq4054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3836
  have eq5751 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq410 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq245 X0 x X2
       grind)
    | exact superpose eq245 eq410
    | exact resolve eq410 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5839 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq5751 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq5751
    | exact resolve eq5751 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5751
  have eq5847 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5839 X0 x
       have i₂ := eq63 X0 x
       grind)
    | exact superpose eq63 eq5839
    | exact resolve eq5839 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5839
  have eq7285 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq525 X0 X1 X2 X3
       have i₂ := eq5847 X0
       grind)
    | exact superpose eq5847 eq525
    | exact resolve eq525 eq5847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq7295 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7285 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq245 X0 x x
       grind)
    | exact superpose eq245 eq7285
    | exact resolve eq7285 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7308 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) = (M.op (M.op X0 (M.op X1 (σ y))) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq61 eq7285
    | exact resolve eq7285 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7456 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 (M.op X2 (M.op X3 (M.op X4 X0)))
       have i₂ := eq7285 X0 X4 X2 X3
       grind)
    | exact superpose eq7285 eq14
    | exact resolve eq14 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7285
  have eq7470 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7456 X0 X1 X2 X3 X4
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq7456
    | exact resolve eq7456 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7456
  have eq7515 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) = (M.op (M.op X0 (M.op X1 (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq237 eq7308
    | exact resolve eq7308 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq7308
  have eq7519 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7295 X0 X1 X2
       have i₂ := eq245 X0 X0 X0
       grind)
    | exact superpose eq245 eq7295
    | exact resolve eq7295 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7295
  have eq7547 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq3858 eq7515
    | exact resolve eq7515 eq3858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3858 eq7515
  have eq7550 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7519 X0 X1 X2
       have i₂ := eq5847 X0
       grind)
    | exact superpose eq5847 eq7519
    | exact resolve eq7519 eq5847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5847 eq7519
  have eq7609 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7550 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7550
    | (have j0 := eq7550 y X0 x
       grind)
    | exact resolve eq7550 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7621 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq7550
    | (have j0 := eq7550 (σ y) X0 (σ x)
       grind)
    | exact resolve eq7550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7638 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7550 (M.op X1 X0) (M.op x X1) X0
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq7550
    | exact resolve eq7550 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7699 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq515 X0
       have i₂ := eq7550 X0 X0 sF4
       grind)
    | exact superpose eq7550 eq515
    | exact resolve eq515 eq7550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq7876 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y))) := by
    first
    | exact superpose eq7621 eq410
    | exact resolve eq410 eq7621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq7904 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq7876
       have i₂ := eq7550 sF3 sF3 sF3
       grind)
    | exact superpose eq7550 eq7876
    | exact resolve eq7876 eq7550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7876
  have eq7907 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq534 X0
       have i₂ := eq7550 X0 X0 X0
       grind)
    | exact superpose eq7550 eq534
    | exact resolve eq534 eq7550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq7923 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq8195 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq7699 eq14
    | exact resolve eq14 eq7699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9331 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X1
       have i₂ := eq7550 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq7550 eq418
    | exact resolve eq418 eq7550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq9367 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 y x X0
       have i₂ := eq9331 X0 x
       grind)
    | exact superpose eq9331 eq59
    | exact resolve eq59 eq9331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9331
  have eq9505 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9367 (M.op X0 X0)
       have i₂ := eq7907 X0
       grind)
    | exact superpose eq7907 eq9367
    | exact resolve eq9367 eq7907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9508 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq9367 (M.op X0 (M.op X0 X0))
       have i₂ := eq245 X0 X0 X0
       grind)
    | exact superpose eq245 eq9367
    | exact resolve eq9367 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9367
  have eq9629 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1330 X0
       have i₂ := eq9508 X0
       grind)
    | exact superpose eq9508 eq1330
    | exact resolve eq1330 eq9508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9635 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq9508 X0
       grind)
    | exact superpose eq9508 eq14
    | exact resolve eq14 eq9508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9649 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq58 sF3
       have i₂ := eq9508 sF3
       grind)
    | exact superpose eq9508 eq58
    | exact resolve eq58 eq9508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9650 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7699 sF4
       have i₂ := eq9508 sF4
       grind)
    | exact superpose eq9508 eq7699
    | exact resolve eq7699 eq9508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7699
  have eq9718 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9508 eq14
    | exact resolve eq14 eq9508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9741 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9718 X0 X1
       have i₂ := eq14 X0 sF0 X0
       grind)
    | exact superpose eq14 eq9718
    | exact resolve eq9718 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9718
  have eq9776 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4054 eq9650
    | exact resolve eq9650 eq4054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9650
  have eq9856 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq7550 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq7550 eq419
    | exact resolve eq419 eq7550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq10125 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq9856 eq59
    | exact resolve eq59 eq9856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9856
  have eq10281 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq10125 (M.op X0 (M.op X0 X0))
       have i₂ := eq245 X0 X0 X0
       grind)
    | exact superpose eq245 eq10125
    | exact resolve eq10125 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq10125
  have eq10699 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq10281 eq14
    | exact resolve eq14 eq10281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10281
  have eq10722 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10699 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq10699
    | exact resolve eq10699 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10699
  have eq11387 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq10722 eq524
    | exact resolve eq524 eq10722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq11388 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4079 eq11387
    | exact resolve eq11387 eq4079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11387
  have eq11389 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7621 eq11388
    | exact resolve eq11388 eq7621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11388
  have eq11420 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq11389 (M.op x (M.op x x)) x sF2
       have i₂ := eq59 x x sF2
       grind)
    | exact superpose eq59 eq11389
    | exact resolve eq11389 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11389
  have eq12946 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq9776 eq11420
    | exact resolve eq11420 eq9776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11420
  have eq13305 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq415 X0 X1 X2 X3
       have i₂ := eq7550 X0 X0 (M.op X2 (M.op X3 X2))
       grind)
    | exact superpose eq7550 eq415
    | exact resolve eq415 eq7550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq13647 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X1 x X2
       have i₂ := eq13305 X2 X0 X1 x
       grind)
    | exact superpose eq13305 eq59
    | exact resolve eq59 eq13305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq13305
  have eq17900 : (M.op y y) = (τ (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq16
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq17938 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq112 eq17900
    | exact resolve eq17900 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq17900
  have eq21634 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 x
       have i₂ := eq7550 X0 X0 x
       grind)
    | exact superpose eq7550 eq545
    | exact resolve eq545 eq7550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq21635 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21634 X0 X1
       have i₂ := eq7907 X0
       grind)
    | exact superpose eq7907 eq21634
    | exact resolve eq21634 eq7907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7907 eq21634
  have eq25023 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq786 x y
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq786
    | (have j0 := eq786 x y
       grind)
    | exact resolve eq786 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq25110 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25023
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25023
    | exact resolve eq25023 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25023
  have eq25241 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25110
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq25110
    | exact resolve eq25110 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25110
  have eq25343 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25241
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25241
    | exact resolve eq25241 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25241
  have eq25444 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25343
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25343
    | exact resolve eq25343 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25343
  have eq25545 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25444
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25444
    | exact resolve eq25444 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25444
  have eq25644 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq25545
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25545
    | exact resolve eq25545 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25545
  have eq25743 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq25644
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25644
    | exact resolve eq25644 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25644
  have eq25806 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq25743
    | exact resolve eq25743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25743
  have eq27870 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = (M.op (M.op X2 (k X0 (M.op X0 X0))) (M.op X1 X1)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq498 X0 X1 X2
       have i₂ := eq7550 X1 X1 (M.op X0 X0)
       grind)
    | exact superpose eq7550 eq498
    | (have j0 := eq498 X0 X1 X2
       grind)
    | exact resolve eq498 eq7550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq29328 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ y))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq9776 eq7547
    | exact resolve eq7547 eq9776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7547
  have eq32547 : ∀ X0 : G, (M.op (M.op X0 X0) (k X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X0 X0) X0))) ∨ (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq858 X0
       have i₂ := eq27870 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq27870 eq858
    | (have j0 := eq858 X0
       have j1 := eq27870 X0 x x
       grind)
    | exact resolve eq858 eq27870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq27870
  have eq32631 : ∀ X0 : G, (M.op (M.op X0 X0) (k X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X0 X0) X0))) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq32547 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32547
  have eq32685 : ∀ X0 : G, (M.op (M.op X0 X0) (k X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq32631 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq32631
    | (have j0 := eq32631 X0
       grind)
    | exact resolve eq32631 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32631
  have eq32736 : ∀ X0 : G, (M.op (M.op X0 X0) (k X0 (M.op X0 X0))) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq32685 X0
       have i₂ := eq1330 X0
       grind)
    | exact superpose eq1330 eq32685
    | (have j0 := eq32685 X0
       grind)
    | exact resolve eq32685 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32685
  have eq42532 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq519 X0 X1 X2 X3 X4
       have i₂ := eq7550 X0 X0 (M.op X1 (M.op X2 X1))
       grind)
    | exact superpose eq7550 eq519
    | exact resolve eq519 eq7550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq7550
  have eq44448 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq231 eq42532
    | exact resolve eq42532 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq42532
  have eq44744 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq10722 eq44448
    | exact resolve eq44448 eq10722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44448
  have eq45037 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq4079 eq44744
    | exact resolve eq44744 eq4079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4079 eq44744
  have eq45160 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq9776 eq45037
    | exact resolve eq45037 eq9776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9776 eq45037
  have eq45225 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq29328 eq45160
    | exact resolve eq45160 eq29328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29328 eq45160
  have eq45264 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq10722 eq45225
    | exact resolve eq45225 eq10722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45225
  have eq45277 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq7621 eq45264
    | exact resolve eq45264 eq7621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7621 eq45264
  have eq45280 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq7904 eq45277
    | exact resolve eq45277 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7904 eq45277
  have eq45281 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq45280 X0 X1
       have i₂ := eq9508 sF3
       grind)
    | exact superpose eq9508 eq45280
    | exact resolve eq45280 eq9508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9508 eq45280
  have eq46701 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq45281 eq14
    | exact resolve eq14 eq45281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45281
  have eq46765 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ x)))) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9649 eq46701
    | exact resolve eq46701 eq9649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9649 eq46701
  have eq56701 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq7638 y X0
       have i₂ := eq9741 (M.op X0 y) X0
       grind)
    | (have i₁ := eq7638 y x
       have i₂ := eq9741 (M.op x y) x
       grind)
    | exact superpose eq9741 eq7638
    | exact resolve eq7638 eq9741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9741
  have eq56702 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq10722 eq7638
    | exact resolve eq7638 eq10722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10722
  have eq64599 : ∀ X0 : G, (M.op y (M.op X0 (M.op x y))) = (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9505 (M.op X0 sF0)
       have i₂ := eq13647 X0 sF0 (M.op X0 sF0)
       grind)
    | exact superpose eq13647 eq9505
    | exact resolve eq9505 eq13647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9505 eq13647
  have eq64712 : ∀ X0 : G, (M.op y (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq64599 x
       have i₂ := eq7638 sF0 x
       grind)
    | exact superpose eq7638 eq64599
    | exact resolve eq64599 eq7638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64599
  have eq106936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq106946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq106936
    | exact resolve eq106936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106936
  have eq106957 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq106946
       have r₂ := eq28
       grind)
    | exact resolve eq106946 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106946
  have eq106970 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq106957 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq106957
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq106957
       grind)
    | exact resolve eq13 eq106957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106957
  have eq107027 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq106970
  have eq107118 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq107027 eq100
    | exact resolve eq100 eq107027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq107027
  have eq107147 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq107118
    | exact resolve eq107118 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107118
  have eq107150 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq107147
       have r₂ := eq13 y x
       grind)
    | exact resolve eq107147 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107147
  have eq107551 : (σ y) = (k (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq107150 eq1473
    | exact resolve eq1473 eq107150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107615 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq107150 eq63
    | exact resolve eq63 eq107150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107150
  have eq107683 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq107615
    | exact resolve eq107615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107615
  have eq107729 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq107683
       grind)
    | exact superpose eq107683 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq107683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107683
  have eq107739 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq107729
  have eq107749 : y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq107739
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107739
    | exact resolve eq107739 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107739
  have eq108195 : (τ (σ y)) = (k x y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq107551 eq56
    | exact resolve eq56 eq107551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107551
  have eq108220 : y = (k x y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq108195
    | exact resolve eq108195 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108195
  have eq108619 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq107749
       grind)
    | exact superpose eq107749 eq57
    | exact resolve eq57 eq107749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq107749
  have eq108724 : x = (M.op y (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56701 eq108619
    | exact resolve eq108619 eq56701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56701 eq108619
  have eq108749 : x = (M.op y (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108724
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108724
    | exact resolve eq108724 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108724
  have eq109796 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq108749 eq60
    | exact resolve eq60 eq108749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108749
  have eq109958 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109796 x
       have i₂ := eq63 x x
       grind)
    | exact superpose eq63 eq109796
    | exact resolve eq109796 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109796
  have eq110692 : x = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1330 x
       have i₂ := eq109958
       grind)
    | exact superpose eq109958 eq1330
    | exact resolve eq1330 eq109958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109958
  have eq110891 : x = (M.op y y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110692
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110692
    | exact resolve eq110692 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110692
  have eq112005 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63 y y
       have i₂ := eq110891
       grind)
    | exact superpose eq110891 eq63
    | exact resolve eq63 eq110891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110891
  have eq112078 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112005
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112005
    | exact resolve eq112005 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112005
  have eq112079 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq112078
  have eq112119 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112079 eq7609
    | exact resolve eq7609 eq112079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7609
  have eq112127 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112079 eq64712
    | exact resolve eq64712 eq112079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112138 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112079 eq63
    | exact resolve eq63 eq112079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112149 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112079 eq7638
    | exact resolve eq7638 eq112079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7638
  have eq112162 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112079 eq21635
    | exact resolve eq21635 eq112079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21635
  have eq112200 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op (M.op (M.op x y) x) (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3915 eq112162
    | exact resolve eq112162 eq3915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112162
  have eq112215 : (M.op y (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3915 eq112138
    | exact resolve eq112138 eq3915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3915 eq112138
  have eq112218 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112119
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112119
    | exact resolve eq112119 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112119
  have eq112225 : y = (M.op (M.op x y) (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60 eq112200
    | exact resolve eq112200 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq112200
  have eq112236 : y = (M.op y (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64712 eq112225
    | exact resolve eq112225 eq64712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64712 eq112225
  have eq113053 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112149 eq112127
    | exact resolve eq112127 eq112149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112127 eq112149
  have eq113125 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq113053
  have eq113312 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112215 eq112236
    | exact resolve eq112236 eq112215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112215 eq112236
  have eq113407 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq113312
  have eq117299 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112079 eq113407
    | exact resolve eq113407 eq112079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112079 eq113407
  have eq117379 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq117299
  have eq117532 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq113125
       have i₂ := eq117379
       grind)
    | exact superpose eq117379 eq113125
    | exact resolve eq113125 eq117379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113125
  have eq117545 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq117379
       grind)
    | exact superpose eq117379 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq117379
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq117379
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq117379
       grind)
    | exact resolve eq13 eq117379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117379
  have eq117603 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq117545
  have eq117605 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq117532
  have eq117687 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq117603
       grind)
    | exact superpose eq117603 eq90
    | exact resolve eq90 eq117603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq117603
  have eq117722 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq117687
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq117687
    | exact resolve eq117687 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117687
  have eq117775 : (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq117605
  have eq118059 : x = (M.op x y) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq117775
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq117775
    | exact resolve eq117775 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117775
  have eq118060 : (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq118059
  have eq118501 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117722 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117722
  have eq118512 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq118501
    | exact resolve eq118501 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118501
  have eq118513 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq118512
  have eq121274 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq118060
       grind)
    | exact superpose eq118060 eq45
    | exact resolve eq45 eq118060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118060
  have eq129848 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121274
       have i₂ := eq112218
       grind)
    | exact superpose eq112218 eq121274
    | exact resolve eq121274 eq112218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112218 eq121274
  have eq129930 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq129848
  have eq129939 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq129930
    | exact resolve eq129930 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129930
  have eq241635 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118513 eq58
    | exact resolve eq58 eq118513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118513
  have eq241785 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56702 eq241635
    | exact resolve eq241635 eq56702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241635
  have eq241817 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq241785
    | exact resolve eq241785 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241785
  have eq244124 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq241817 eq61
    | exact resolve eq61 eq241817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241817
  have eq244327 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq244124 x
       have i₂ := eq63 sF2 x
       grind)
    | exact superpose eq63 eq244124
    | exact resolve eq244124 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244124
  have eq246123 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq244327 eq1330
    | exact resolve eq1330 eq244327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330 eq244327
  have eq246400 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq246123
    | exact resolve eq246123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246123
  have eq248147 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq246400 eq247
    | exact resolve eq247 eq246400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246400
  have eq248210 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq248147
  have eq248243 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq248210
       have r₂ := eq52
       grind)
    | exact resolve eq248210 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248210
  have eq248907 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq248243 eq56
    | exact resolve eq56 eq248243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq248243
  have eq248960 : y = (k x y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq248907
    | exact resolve eq248907 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248907
  have eq248964 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | (have r₁ := eq248960
       have r₂ := eq51
       grind)
    | exact resolve eq248960 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248960
  have eq248972 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 ∨ y = (k x y) := by
    intro X0
    first
    | exact superpose eq248964 eq8195
    | exact resolve eq8195 eq248964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8195
  have eq248995 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq248964 eq63
    | exact resolve eq63 eq248964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249008 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ y = (k x y) := by
    first
    | exact superpose eq248964 eq9635
    | exact resolve eq9635 eq248964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9635
  have eq249090 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq12946 eq249008
    | exact resolve eq249008 eq12946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249008
  have eq249100 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq4054 eq248995
    | exact resolve eq248995 eq4054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4054 eq248995
  have eq257935 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq249090 eq248972
    | exact resolve eq248972 eq249090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248972 eq249090
  have eq258064 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (k x y) := by grind
  clear eq257935
  have eq258303 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq249100 eq258064
    | exact resolve eq258064 eq249100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249100 eq258064
  have eq258399 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (k x y) := by grind
  clear eq258303
  have eq258913 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq248964 eq258399
    | exact resolve eq258399 eq248964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248964 eq258399
  have eq259005 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq258913
  have eq263130 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq259005 eq7923
    | exact resolve eq7923 eq259005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7923 eq259005
  have eq263426 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq27 eq263130
    | exact resolve eq263130 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263130
  have eq263577 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq27 eq263426
    | exact resolve eq263426 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263426
  have eq266088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq263577 eq129939
    | exact resolve eq129939 eq263577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129939 eq263577
  have eq266132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq266088
  have eq266148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have r₁ := eq266132
       have r₂ := eq51
       grind)
    | exact resolve eq266132 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq266132
  have eq266152 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq266148
       have r₂ := eq28
       grind)
    | exact resolve eq266148 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266148
  have eq266158 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq266152
       grind)
    | exact superpose eq266152 eq45
    | exact resolve eq45 eq266152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq266152
  have eq266264 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq266158
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq266158
    | exact resolve eq266158 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq266158
  have eq266274 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq266264
       have r₂ := eq52
       grind)
    | exact resolve eq266264 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq266264
  have eq266687 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq25806
       have r₂ := eq266274
       grind)
    | exact resolve eq25806 eq266274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25806
  have eq267223 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq266687 eq247
    | exact resolve eq247 eq266687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq266687
  have eq267286 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq267223
  have eq267287 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq267286
  have eq267636 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq267287 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq267287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267287
  have eq267648 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq267636
    | exact resolve eq267636 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267636
  have eq267649 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq267648
  have eq389881 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq267649 eq58
    | exact resolve eq58 eq267649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq267649
  have eq390067 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56702 eq389881
    | exact resolve eq389881 eq56702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56702 eq389881
  have eq390103 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq390067
    | exact resolve eq390067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390067
  have eq390604 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq390103 eq61
    | exact resolve eq61 eq390103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq390103
  have eq390852 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq390604 x
       have i₂ := eq63 sF2 x
       grind)
    | exact superpose eq63 eq390604
    | exact resolve eq390604 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390604
  have eq391046 : (σ x) = (M.op (σ y) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq390852 eq32736
    | exact resolve eq32736 eq390852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32736 eq390852
  have eq391257 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq266274 eq391046
    | exact resolve eq391046 eq266274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266274 eq391046
  have eq391258 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq391257
  have eq391381 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq391258
    | exact resolve eq391258 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq391258
  have eq391382 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq391381
  have eq391752 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ x)))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq391382 eq7470
    | exact resolve eq7470 eq391382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7470 eq391382
  have eq391858 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46765 eq391752
    | exact resolve eq391752 eq46765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46765 eq391752
  have eq391859 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq391858
  have eq391932 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq391859 eq28
    | exact resolve eq28 eq391859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq391988 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) := by
    first
    | exact superpose eq391859 eq12946
    | exact resolve eq12946 eq391859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12946 eq391859
  have eq392194 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq9629 eq391988
    | exact resolve eq391988 eq9629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9629 eq391988
  have eq392242 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq392194 eq174
    | exact resolve eq174 eq392194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq392194
  have eq392636 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq392242
    | exact resolve eq392242 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392242
  have eq393738 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq392636
       have i₂ := eq17938
       grind)
    | exact superpose eq17938 eq392636
    | exact resolve eq392636 eq17938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17938
  have eq1952157 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1473 y
       have i₂ := eq393738
       grind)
    | exact superpose eq393738 eq1473
    | exact resolve eq1473 eq393738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1952641 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq393738
  have eq1953168 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq392636
       have i₂ := eq1952157
       grind)
    | exact superpose eq1952157 eq392636
    | exact resolve eq392636 eq1952157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392636 eq1952157
  have eq1953238 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq1953168
  have eq1953275 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1953238
       have r₂ := eq1952641
       grind)
    | exact resolve eq1953238 eq1952641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952641 eq1953238
  have eq1953918 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq63 y y
       have i₂ := eq1953275
       grind)
    | exact superpose eq1953275 eq63
    | exact resolve eq63 eq1953275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1953275
  have eq1954205 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1953918
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1953918
    | exact resolve eq1953918 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953918
  have eq1954489 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1954205 eq30
    | exact resolve eq30 eq1954205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1954205
  have eq1955577 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1954489
    | exact resolve eq1954489 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1954489
  have eq1955736 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1955577 eq21
    | exact resolve eq21 eq1955577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955577
  have eq1956579 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1955736
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1955736
    | exact resolve eq1955736 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955736
  have eq1956632 : x = y := by
    first
    | (have r₁ := eq1956579
       have r₂ := eq391932
       grind)
    | exact resolve eq1956579 eq391932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956579
  have eq1956664 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1956632
       grind)
    | exact superpose eq1956632 eq19
    | exact resolve eq19 eq1956632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1956988 : x = (k x x) ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq108220
       have i₂ := eq1956632
       grind)
    | exact superpose eq1956632 eq108220
    | exact resolve eq108220 eq1956632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108220 eq1956632
  have eq1957488 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq1956988
  have eq1957559 : x = (M.op x x) := by
    first
    | (have j1 := eq3991 x
       grind)
    | (have r₁ := eq1957488
       have r₂ := eq3991 x
       grind)
    | exact resolve eq1957488 eq3991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991 eq1957488
  have eq1960601 : x = (M.op x y) := by
    first
    | (have i₁ := eq1957559
       have i₂ := eq1956664
       grind)
    | exact superpose eq1956664 eq1957559
    | exact resolve eq1957559 eq1956664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956664 eq1957559
  have eq1960605 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1960601 eq21
    | exact resolve eq21 eq1960601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1960601
  have eq1961691 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1960605
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1960605
    | exact resolve eq1960605 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1960605
  have eq1961954 : False := by grind
  exact eq1961954

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq13 (M.op X0 X0) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  clear eq37
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X0
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) ≠ X0 ∨ (k (M.op X0 (M.op X2 X0)) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X2 X0)) (M.op X1 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq175 (M.op y y)
       have i₂ := eq16 y y y
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 y
       have i₂ := eq185
       grind)
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq176 (M.op sF3 sF3)
       have i₂ := eq16 sF3 sF3 sF3
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq199 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq194 eq16
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 (M.op X2 X0)
       have i₂ := eq181 X0 X2
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq641 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k (M.op X0 X1) X1)) = X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 (M.op X0 X1) X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 (M.op X0 X1) X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : (M.op x y) = (k y x) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq658
       have i₂ := eq185
       grind)
    | exact superpose eq185 eq658
    | exact resolve eq658 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq718 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq718 X0
       have i₂ := eq181 X0 X0
       grind)
    | exact superpose eq181 eq718
    | (have j0 := eq718 X0
       grind)
    | exact resolve eq718 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq720 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq719
    | (have j0 := eq719 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq719 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq729 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq696
       grind)
    | exact superpose eq696 eq40
    | exact resolve eq40 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq696
  have eq730 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq729
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq729
    | exact resolve eq729 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq732 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq20 eq730
    | exact resolve eq730 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq732 eq673
    | exact resolve eq673 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq735
       have r₂ := eq27
       grind)
    | exact resolve eq735 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq750 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq742 eq28
    | exact resolve eq28 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq742 eq181
    | exact resolve eq181 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq742 eq13
    | exact resolve eq13 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq751
    | exact resolve eq751 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq756 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq750
       have r₂ := eq752
       grind)
    | exact resolve eq750 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq752
  have eq763 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq755 eq181
    | exact resolve eq181 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq763
       have i₂ := eq185
       grind)
    | exact superpose eq185 eq763
    | exact resolve eq763 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq770 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq767
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq767
    | exact resolve eq767 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq773 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq770 eq755
    | exact resolve eq755 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq770
  have eq782 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq773
  have eq786 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq782 eq27
    | exact resolve eq27 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq782 eq194
    | exact resolve eq194 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq794 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq790
    | exact resolve eq790 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq795 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq782 eq794
    | exact resolve eq794 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq794
  have eq800 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq795 eq28
    | exact resolve eq28 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq795 eq13
    | exact resolve eq13 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq806 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq800
       have r₂ := eq802
       grind)
    | exact resolve eq800 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800 eq802
  have eq810 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq806 eq116
    | exact resolve eq116 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq810
    | exact resolve eq810 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq1084 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq756 eq720
    | (have j0 := eq720 (σ y)
       grind)
    | exact resolve eq720 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq1103 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq732 eq1084
    | exact resolve eq1084 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1115 : x = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq742 eq1103
    | exact resolve eq1103 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq1103
  have eq1196 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1115 eq181
    | exact resolve eq181 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1200 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1196
       have i₂ := eq185
       grind)
    | exact superpose eq185 eq1196
    | exact resolve eq1196 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq1196
  have eq1204 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1200
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1200
    | exact resolve eq1200 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1211 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1204 eq1115
    | exact resolve eq1115 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq1204
  have eq1221 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1211
  have eq1226 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1221 eq32
    | exact resolve eq32 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1232 : (k y y) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1221 eq116
    | exact resolve eq116 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1243 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1221 eq732
    | exact resolve eq732 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq1250 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1221 eq806
    | exact resolve eq806 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq1221
  have eq1255 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1250
  have eq1262 : (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1255 eq1243
    | exact resolve eq1243 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243 eq1255
  have eq1271 : (k x x) = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq98 eq1232
    | exact resolve eq1232 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1232
  have eq1277 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1226
    | exact resolve eq1226 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1226
  have eq1279 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1262
       have r₂ := eq786
       grind)
    | exact resolve eq1262 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq1262
  have eq1283 : x = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq817 eq1271
    | exact resolve eq1271 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1284 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1277 eq1279
    | exact resolve eq1279 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq1369 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq685 x
       have i₂ := eq1283
       grind)
    | exact superpose eq1283 eq685
    | (have j0 := eq685 x
       grind)
    | (have r₁ := eq685 x
       have r₂ := eq1283
       grind)
    | exact resolve eq685 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1370 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1369
  have eq1374 : y = (M.op x (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1284 eq178
    | exact resolve eq178 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1378 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1284 eq16
    | exact resolve eq16 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1381 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1370 eq1378
    | exact resolve eq1378 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1383 : x = (M.op x (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1277 eq1374
    | exact resolve eq1374 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq1374
  have eq2490 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op x (M.op x y)) x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1383 eq16
    | exact resolve eq16 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383
  have eq2502 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1381 eq2490
    | exact resolve eq2490 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381 eq2490
  have eq2505 : (M.op x x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2502 x
       have i₂ := eq181 x x
       grind)
    | exact superpose eq181 eq2502
    | exact resolve eq2502 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502
  have eq2508 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1370 eq2505
    | exact resolve eq2505 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505
  have eq2518 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2508 eq16
    | exact resolve eq16 eq2508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508
  have eq2533 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1284 eq2518
    | exact resolve eq2518 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284 eq2518
  have eq2535 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2533 x
       have i₂ := eq181 x x
       grind)
    | exact superpose eq181 eq2533
    | exact resolve eq2533 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533
  have eq2561 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1370
       have i₂ := eq2535
       grind)
    | exact superpose eq2535 eq1370
    | exact resolve eq1370 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370 eq2535
  have eq2574 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2561
  have eq2580 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2574 eq29
    | exact resolve eq29 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq2588 : (k (M.op x y) (M.op x y)) = (τ (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2574 eq134
    | exact resolve eq134 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq2574
  have eq2593 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq2588
    | exact resolve eq2588 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq2588
  have eq2601 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq2580
    | exact resolve eq2580 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580
  have eq2602 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq817 eq2593
    | exact resolve eq2593 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq2593
  have eq2610 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2601
       grind)
    | exact superpose eq2601 eq18
    | exact resolve eq18 eq2601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2614 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op x y) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq2601
       grind)
    | exact superpose eq2601 eq175
    | exact resolve eq175 eq2601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2601
  have eq3129 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2610 eq641
    | exact resolve eq641 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3196 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2602 eq3129
    | exact resolve eq3129 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129
  have eq3230 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3196 x
       have i₂ := eq181 x x
       grind)
    | exact superpose eq181 eq3196
    | exact resolve eq3196 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196
  have eq3944 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3230 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq3230
       grind)
    | exact resolve eq13 eq3230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230
  have eq3956 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq3944
  have eq3969 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2602 eq3956
    | exact resolve eq3956 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602 eq3956
  have eq3970 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq3969
  have eq3991 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq181 x x
       have i₂ := eq3970
       grind)
    | exact superpose eq3970 eq181
    | exact resolve eq181 eq3970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3970
  have eq4013 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3991 eq2614
    | exact resolve eq2614 eq3991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614 eq3991
  have eq4032 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq4013
  have eq4043 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2610 eq4032
    | exact resolve eq4032 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4032
  have eq4087 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4043 eq181
    | exact resolve eq181 eq4043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4043
  have eq4104 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2610 eq4087
    | exact resolve eq4087 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610 eq4087
  have eq4105 : x = (M.op x y) := by grind
  clear eq4104
  have eq4360 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4105
       grind)
    | exact superpose eq4105 eq18
    | exact resolve eq18 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4361 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4105
       grind)
    | exact superpose eq4105 eq22
    | exact resolve eq22 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4105
  have eq4374 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4361 eq20
    | exact resolve eq20 eq4361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4384 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4361 eq352
    | exact resolve eq352 eq4361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq4361
  have eq4451 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq4360 eq191
    | exact resolve eq191 eq4360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq4360
  have eq4481 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | exact superpose eq4451 eq16
    | exact resolve eq16 eq4451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4451
  have eq4501 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4481 x
       have i₂ := eq181 y x
       grind)
    | exact superpose eq181 eq4481
    | exact resolve eq4481 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4481
  have eq4518 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq4501
       grind)
    | exact superpose eq4501 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq4501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4521 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq4501
       grind)
    | exact superpose eq4501 eq28
    | exact resolve eq28 eq4501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4501
  have eq4533 : (M.op x y) = (k y y) := by
    first
    | (have r₁ := eq4518
       have r₂ := eq4521
       grind)
    | exact resolve eq4518 eq4521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518 eq4521
  have eq4554 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq4533
       grind)
    | exact superpose eq4533 eq41
    | exact resolve eq41 eq4533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4533
  have eq4564 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq4554
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4554
    | exact resolve eq4554 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4554
  have eq4568 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq4564
    | exact resolve eq4564 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4564
  have eq4570 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq4374 eq4568
    | exact resolve eq4568 eq4374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4568
  have eq4621 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4570 eq720
    | (have j0 := eq720 (σ y)
       grind)
    | exact resolve eq720 eq4570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq4919 : (k (τ (σ y)) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq673 eq4384
    | exact resolve eq4384 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq4964 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq4919
    | exact resolve eq4919 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4919
  have eq5300 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4621 eq4384
    | exact resolve eq4384 eq4621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4384 eq4621
  have eq5307 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq32 eq5300
    | exact resolve eq5300 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq5300
  have eq5329 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5307 eq199
    | exact resolve eq199 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5334 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5307 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq5307
       grind)
    | exact resolve eq13 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5341 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k (M.op (σ y) (σ y)) (M.op X0 (σ y))) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5307 eq184
    | exact resolve eq184 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq5348 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq5334
  have eq5351 : ∀ X0 : G, (σ y) = (k (M.op (σ y) (σ y)) (M.op X0 (σ y))) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq5341 X0
       grind)
    | (have r₁ := eq5341 X0
       have r₂ := eq5307
       grind)
    | exact resolve eq5341 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5341
  have eq5355 : y = (k y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4570 eq5348
    | exact resolve eq5348 eq4570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5348
  have eq5357 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5307 eq5329
    | exact resolve eq5329 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5329
  have eq5361 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ y))) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5307 eq5351
    | exact resolve eq5351 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5351
  have eq5365 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5355 eq5357
    | exact resolve eq5357 eq5355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5357
  have eq5367 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5355 eq5361
    | exact resolve eq5361 eq5355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5361
  have eq10513 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5365 eq179
    | exact resolve eq179 eq5365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10517 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5365 eq28
    | (have j0 := eq28 (σ x) (M.op X0 (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq28 eq5365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10532 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5355 eq10513
    | exact resolve eq10513 eq5355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10513
  have eq10536 : (σ x) = (k (σ x) (σ x)) ∨ y = (k y (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5365 eq5367
    | exact resolve eq5367 eq5365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5365 eq5367
  have eq10543 : (σ x) = (k (σ x) (σ x)) ∨ y = (k y (M.op x y)) := by grind
  clear eq10536
  have eq10562 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq10543 eq685
    | (have j0 := eq685 (σ x)
       grind)
    | (have r₁ := eq685 (σ x)
       have r₂ := eq10543
       grind)
    | exact resolve eq685 eq10543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq10543
  have eq10565 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y (M.op x y)) := by grind
  clear eq10562
  have eq10977 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (k (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq10532 eq641
    | exact resolve eq641 eq10532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq10532
  have eq10981 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq10517 eq10977
    | (have j1 := eq10517 (σ x)
       grind)
    | exact resolve eq10977 eq10517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10517 eq10977
  have eq10989 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq10981 x
       have i₂ := eq181 sF2 x
       grind)
    | exact superpose eq181 eq10981
    | exact resolve eq10981 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10981
  have eq10990 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k y (M.op x y)) := by grind
  clear eq10989
  have eq10996 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq10565 eq10990
    | exact resolve eq10990 eq10565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10565 eq10990
  have eq11008 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq10996 eq199
    | exact resolve eq199 eq10996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq10996
  have eq11031 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5307 eq11008
    | exact resolve eq11008 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11008
  have eq11032 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5307 eq11031
    | exact resolve eq11031 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5307 eq11031
  have eq11033 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq11032
    | exact resolve eq11032 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11032
  have eq11034 : y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5355 eq11033
    | exact resolve eq11033 eq5355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5355 eq11033
  have eq11046 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11034 eq4964
    | exact resolve eq4964 eq11034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4964 eq11034
  have eq11428 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11046 eq181
    | exact resolve eq181 eq11046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11046
  have eq11437 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11428
    | exact resolve eq11428 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11428
  have eq11438 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11437
  have eq11546 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11438 eq14
    | exact resolve eq14 eq11438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11438
  have eq11556 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11546
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11546
    | exact resolve eq11546 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11546
  have eq11559 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11556 eq179
    | exact resolve eq179 eq11556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq11573 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq11834 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11559 X0
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq11559
    | (have j1 := eq28 (σ y) (σ y)
       grind)
    | exact resolve eq11559 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11559
  have eq11863 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq4570 eq11834
    | exact resolve eq11834 eq4570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11834
  have eq11869 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11863 x
       have i₂ := eq181 sF2 x
       grind)
    | exact superpose eq181 eq11863
    | exact resolve eq11863 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11863
  have eq26718 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11869 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq11869
       grind)
    | exact resolve eq13 eq11869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11869
  have eq26742 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq26718
  have eq26761 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4570 eq26742
    | exact resolve eq26742 eq4570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4570 eq26742
  have eq26782 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26761
       have r₂ := eq11573
       grind)
    | exact resolve eq26761 eq11573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26761
  have eq26808 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26782 eq219
    | exact resolve eq219 eq26782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq26816 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26782 eq180
    | exact resolve eq180 eq26782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq26817 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26782 eq181
    | exact resolve eq181 eq26782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq26782
  have eq26845 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq26816
    | (have j0 := eq26816 X0 X1
       grind)
    | exact resolve eq26816 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26816
  have eq26849 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq26808
    | (have j0 := eq26808 X0 X1
       grind)
    | exact resolve eq26808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq26808
  have eq26859 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq11556 eq26845
    | exact resolve eq26845 eq11556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26845
  have eq26862 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq11556 eq26849
    | exact resolve eq26849 eq11556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11556 eq26849
  have eq26866 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26817 eq26859
    | exact resolve eq26859 eq26817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26817 eq26859
  have eq26868 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f26868_13 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f26868_14 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f26868_23 : (σ y) ≠ (σ x) := by grind
    have f26868_24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f26868_27 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f26868_14 X0 X1
         grind)
      | (have r₁ := f26868_14 X0 X1
         have r₂ := f26868_24
         grind)
      | exact resolve f26868_14 f26868_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f26868_28 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f26868_13 X0 X1
         grind)
      | (have r₁ := f26868_13 X0 X1
         have r₂ := f26868_24
         grind)
      | exact resolve f26868_13 f26868_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f26868_29 : (σ y) = (σ x) := by
      first
      | (have i₁ := f26868_28 x x
         have i₂ := f26868_27 x x
         grind)
      | exact superpose f26868_27 f26868_28
      | exact resolve f26868_28 f26868_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f26868_30 : False := by
      first
      | (have r₁ := f26868_29
         have r₂ := f26868_23
         grind)
      | exact resolve f26868_29 f26868_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f26868_30
  clear eq26862 eq26866
  have eq26870 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26868
       have r₂ := eq11573
       grind)
    | exact resolve eq26868 eq11573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11573 eq26868
  have eq26875 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq26870 eq27
    | exact resolve eq27 eq26870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq26870
  have eq26918 : False := by grind
  exact eq26918

/-- `Equation1577`: `x = (y ◇ z) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pyx_pyx_pxy_Equation1577 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1577 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1577.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  clear eq44
  have eq51 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) (M.op (M.op X1 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) (M.op X1 X2) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq81 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq79 (σ X0)
       grind)
    | exact superpose eq79 eq10
    | exact resolve eq10 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq79 sF2
       grind)
    | exact superpose eq79 eq50
    | exact resolve eq50 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq84 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq83
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq83
    | exact resolve eq83 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq86 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq81
    | exact resolve eq81 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq93 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq79 sF3
       grind)
    | exact superpose eq79 eq77
    | exact resolve eq77 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq94 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq79 y
       grind)
    | exact superpose eq79 eq93
    | exact resolve eq93 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
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
  clear eq45
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq109
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq109
    | exact resolve eq109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq121 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq16
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq79 sF1
       grind)
    | exact superpose eq79 eq137
    | exact resolve eq137 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq79 sF0
       grind)
    | exact superpose eq79 eq140
    | exact resolve eq140 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq163 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq241 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) X0) y) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq79 (τ X0)
       grind)
    | exact superpose eq79 eq35
    | exact resolve eq35 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq300 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq289 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq289
    | exact resolve eq289 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq302 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq300
    | exact resolve eq300 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq300
  have eq402 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq54 eq233
    | exact resolve eq233 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq581 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq237 eq57
    | exact resolve eq57 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (M.op X1 X0) X1
       have i₂ := eq57 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op (M.op X2 X1) (M.op X2 X0)) X2 X1
       have i₂ := eq14 X0 (M.op X2 X1) X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq241 (M.op x X0)
       have i₂ := eq57 (M.op x X0) x X0
       grind)
    | exact superpose eq57 eq241
    | exact resolve eq241 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq589 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq245 (M.op sF2 x)
       have i₂ := eq57 (M.op sF2 x) sF2 x
       grind)
    | exact superpose eq57 eq245
    | exact resolve eq245 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq668 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) X3)) (M.op (M.op X2 (M.op X0 X1)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X1 X2 (M.op (M.op X3 X0) X3) X4
       have i₂ := eq57 X1 X3 X0
       grind)
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X2 X3 (M.op X2 (M.op (M.op X3 X1) X0))
       have i₂ := eq14 X0 X2 (M.op X3 X1)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op (M.op X0 (M.op x y)) X1)) = (M.op (M.op X2 y) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) = (M.op (M.op X2 (σ y)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op x (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq792 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X3 X4) (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op X3 (M.op X4 X0)) (M.op X3 X4) X1 X2
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op (M.op X3 X0) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X3 X0 (M.op X3 X2)
       have i₂ := eq56 X2 X3 X0 X1
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq581 (M.op sF3 (M.op sF4 X0))
       have i₂ := eq14 X0 sF3 sF4
       grind)
    | exact superpose eq14 eq581
    | exact resolve eq581 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x y
       have i₂ := eq588 X0
       grind)
    | exact superpose eq588 eq53
    | exact resolve eq53 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq589 eq53
    | exact resolve eq53 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq1135 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1020 (M.op x x)
       have i₂ := eq57 sF0 x x
       grind)
    | exact superpose eq57 eq1020
    | exact resolve eq1020 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1143 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op X0 x)) y) := by
    intro X0
    first
    | exact superpose eq1020 eq14
    | exact resolve eq14 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1365 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq237 eq1042
    | exact resolve eq1042 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1374 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X0 (σ x))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1042 eq14
    | exact resolve eq14 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1042 eq967
    | exact resolve eq967 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq1042
  have eq1400 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq237 eq1399
    | exact resolve eq1399 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq1399
  have eq1518 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 (M.op x X1)) (M.op X0 y)) := by
    intro X0 X1
    first
    | exact superpose eq1135 eq14
    | exact resolve eq14 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1525 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op x (M.op X1 y)) := by
    intro X1
    first
    | (have i₁ := eq1518 x X1
       have i₂ := eq56 y x x X1
       grind)
    | exact superpose eq56 eq1518
    | exact resolve eq1518 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1518
  have eq1538 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq53 x X0 X0 y
       have i₂ := eq1143 X0
       grind)
    | exact superpose eq1143 eq53
    | exact resolve eq53 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1637 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1374 eq53
    | exact resolve eq53 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1727 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq585 eq582
    | exact resolve eq582 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq1909 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ y) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq1727 eq57
    | exact resolve eq57 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2102 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1727 eq583
    | exact resolve eq583 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq1727
  have eq4315 : ∀ X0 : G, y = (M.op x (M.op (σ (M.op X0 X0)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1538 (σ X0)
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq1538
    | exact resolve eq1538 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq4671 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ (M.op X0 X0)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1637 (σ X0)
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq1637
    | exact resolve eq1637 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq1637
  have eq5276 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq783 (M.op x y) y
       have i₂ := eq588 y
       grind)
    | exact superpose eq588 eq783
    | exact resolve eq783 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq783
  have eq5339 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq5276
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq5276
    | exact resolve eq5276 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5276
  have eq6946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq6946
    | exact resolve eq6946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6946
  have eq6950 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq6947
       have r₂ := eq28
       grind)
    | exact resolve eq6947 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6947
  have eq6952 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq6950
    | exact resolve eq6950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6950
  have eq7011 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6952 eq68
    | (have r₁ := eq68
       have r₂ := eq6952
       grind)
    | exact resolve eq68 eq6952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq7019 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (σ x)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6952 eq581
    | exact resolve eq581 eq6952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq7024 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6952 eq1365
    | exact resolve eq1365 eq6952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365 eq6952
  have eq7041 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq7011
  have eq7048 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1909 eq7019
    | exact resolve eq7019 eq1909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909 eq7019
  have eq7237 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7041 eq110
    | exact resolve eq110 eq7041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq7041
  have eq7241 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7237
  have eq7254 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7241 eq55
    | exact resolve eq55 eq7241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq7446 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7048 eq1374
    | exact resolve eq1374 eq7048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq7507 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7446
       have i₂ := eq582 sF2 sF4 sF3
       grind)
    | exact superpose eq582 eq7446
    | exact resolve eq7446 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7446
  have eq7632 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7241 eq7024
    | exact resolve eq7024 eq7241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7024 eq7241
  have eq7661 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq7632
  have eq7861 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7661 eq2102
    | exact resolve eq2102 eq7661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102 eq7661
  have eq13942 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7861 eq7048
    | exact resolve eq7048 eq7861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7048
  have eq13977 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13942
  have eq14001 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1400 eq13977
    | exact resolve eq13977 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400 eq13977
  have eq14041 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14001 eq7254
    | exact resolve eq7254 eq14001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7254 eq14001
  have eq14083 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14041
  have eq14884 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14083 eq163
    | exact resolve eq163 eq14083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq14083
  have eq14941 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq14884
    | exact resolve eq14884 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14884
  have eq14947 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14941 eq402
    | exact resolve eq402 eq14941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq14941
  have eq16013 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq14947
       grind)
    | exact superpose eq14947 eq94
    | exact resolve eq94 eq14947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq14947
  have eq16086 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16013
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16013
    | exact resolve eq16013 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16013
  have eq17247 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16086 eq7861
    | exact resolve eq7861 eq16086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7861 eq16086
  have eq17301 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq17247
  have eq17343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17301 eq7507
    | exact resolve eq7507 eq17301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7507 eq17301
  have eq17382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq17343
  have eq17399 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq17382
       have r₂ := eq28
       grind)
    | exact resolve eq17382 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17382
  have eq17412 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17399 eq30
    | exact resolve eq30 eq17399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17399
  have eq17476 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq17412
    | exact resolve eq17412 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17412
  have eq17477 : x = (M.op x y) ∨ x = y := by grind
  clear eq17476
  have eq17819 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq17477 eq21
    | exact resolve eq21 eq17477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17822 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17477 eq54
    | exact resolve eq54 eq17477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq17864 : (M.op x x) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq17477 eq5339
    | exact resolve eq5339 eq17477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5339 eq17477
  have eq17868 : (M.op x x) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq17864
       have i₂ := eq1525 x
       grind)
    | exact superpose eq1525 eq17864
    | exact resolve eq17864 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq17864
  have eq17891 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq17819
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17819
    | exact resolve eq17819 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17819
  have eq18664 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op x (M.op (M.op X0 X1) (M.op X1 (M.op x x)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq17868 eq813
    | exact resolve eq813 eq17868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17868
  have eq18669 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18664 X0 x
       have i₂ := eq813 x x x X0
       grind)
    | exact superpose eq813 eq18664
    | exact resolve eq18664 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq18664
  have eq20055 : ∀ X0 X1 X2 : G, (M.op (M.op X2 y) (M.op X2 X1)) = (M.op (M.op x y) (M.op (M.op (M.op X0 x) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 x X0 X2
       have i₂ := eq697 X0 sF0 (M.op x x) x
       grind)
    | (have i₁ := eq757 X2 X0 X2
       have i₂ := eq697 X0 (M.op X2 x) X2 sF0
       grind)
    | exact superpose eq697 eq757
    | exact resolve eq757 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq20056 : ∀ X1 X2 : G, (M.op (M.op X2 y) (M.op X2 X1)) = (M.op (M.op x y) (M.op x X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq20055 x X1 X2
       have i₂ := eq57 X1 x x
       grind)
    | exact superpose eq57 eq20055
    | exact resolve eq20055 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20055
  have eq20927 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ y)) (M.op X2 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 (σ x)) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq758 x X0 X2
       have i₂ := eq697 X0 sF4 (M.op x sF2) x
       grind)
    | (have i₁ := eq758 X2 X0 X2
       have i₂ := eq697 X0 (M.op X2 sF2) X2 sF4
       grind)
    | exact superpose eq697 eq758
    | exact resolve eq758 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq20928 : ∀ X1 X2 : G, (M.op (M.op X2 (σ y)) (M.op X2 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq20927 X1 x X2
       have i₂ := eq57 x X1 sF2
       grind)
    | exact superpose eq57 eq20927
    | exact resolve eq20927 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20927
  have eq34181 : y = (M.op x (M.op (σ y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq4315 (M.op x x)
       have i₂ := eq17822 x
       grind)
    | exact superpose eq17822 eq4315
    | exact resolve eq4315 eq17822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq34183 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq4671 (M.op x x)
       have i₂ := eq17822 x
       grind)
    | exact superpose eq17822 eq4671
    | exact resolve eq4671 eq17822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671 eq17822
  have eq34269 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq34183
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34183
    | exact resolve eq34183 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34183
  have eq34270 : y = (M.op x (M.op (σ y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq34181
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34181
    | exact resolve eq34181 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34181
  have eq35321 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq17891 eq34269
    | exact resolve eq34269 eq17891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17891 eq34269
  have eq35385 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y := by grind
  clear eq35321
  have eq35445 : y = (M.op x (M.op (σ y) x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18669 eq34270
    | exact resolve eq34270 eq18669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18669 eq34270
  have eq35495 : y = (M.op x (M.op (σ y) x)) ∨ x = y := by grind
  clear eq35445
  have eq36585 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) X0) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq35385 eq582
    | exact resolve eq582 eq35385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35385
  have eq36628 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq36585 X0
       have i₂ := eq57 X0 sF3 sF4
       grind)
    | exact superpose eq57 eq36585
    | exact resolve eq36585 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36585
  have eq36660 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X3 X0) X3))) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq668 X0 X1 X2 X3 X4
       have i₂ := eq697 X4 (M.op X2 (M.op (M.op X3 X0) X3)) X2 (M.op X0 X1)
       grind)
    | (have i₁ := eq668 X0 X1 X3 X3 X0
       have i₂ := eq697 X0 (M.op X0 X1) (M.op X3 (M.op (M.op X3 X0) X3)) X3
       grind)
    | exact superpose eq697 eq668
    | exact resolve eq668 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq697
  have eq36677 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq35495 eq582
    | exact resolve eq582 eq35495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq35495
  have eq39285 : (M.op y y) = (τ (M.op y (σ y))) ∨ x = y := by
    first
    | exact superpose eq36677 eq121
    | exact resolve eq121 eq36677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq36677
  have eq44878 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X2 (M.op (M.op (M.op X3 X0) X3) (M.op X0 (M.op X1 X4)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36660 X0 X1 X2 X3 X4
       have i₂ := eq792 X4 X2 (M.op (M.op X3 X0) X3) X0 X1
       grind)
    | exact superpose eq792 eq36660
    | exact resolve eq36660 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq36660
  have eq44879 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X0 (M.op X0 (M.op X1 X4)))))) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq44878 X0 X1 X2 x X4
       have i₂ := eq57 (M.op X0 (M.op X1 X4)) x X0
       grind)
    | exact superpose eq57 eq44878
    | exact resolve eq44878 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq44878
  have eq63406 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op y (σ y)) (M.op y (σ y))) ∨ x = y := by
    first
    | exact superpose eq39285 eq302
    | exact resolve eq302 eq39285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq39285
  have eq63424 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) ∨ x = y := by
    first
    | exact superpose eq20928 eq63406
    | exact resolve eq63406 eq20928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20928 eq63406
  have eq63427 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq63424
       have i₂ := eq20056 y y
       grind)
    | exact superpose eq20056 eq63424
    | exact resolve eq63424 eq20056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20056 eq63424
  have eq63429 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq63427
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq63427
    | exact resolve eq63427 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63427
  have eq63431 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq27 eq63429
    | exact resolve eq63429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63429
  have eq63432 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq142 eq63431
    | exact resolve eq63431 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq63431
  have eq63445 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq63432 eq36628
    | exact resolve eq36628 eq63432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36628 eq63432
  have eq63535 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq63445
  have eq64103 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op (σ (M.op x y)) (σ (M.op x y)))))))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq63535 eq44879
    | exact resolve eq44879 eq63535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63535
  have eq64108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq64103 x x
       have i₂ := eq44879 x sF1 x sF1
       grind)
    | (have i₁ := eq64103 x x
       have i₂ := eq44879 x x x (M.op sF1 (M.op x (M.op x (M.op x (M.op x (M.op sF1 sF1))))))
       grind)
    | exact superpose eq44879 eq64103
    | exact resolve eq64103 eq44879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44879 eq64103
  have eq64151 : x = y := by
    first
    | (have r₁ := eq64108
       have r₂ := eq28
       grind)
    | exact resolve eq64108 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64108
  have eq64300 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq64151
       grind)
    | exact superpose eq64151 eq19
    | exact resolve eq19 eq64151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq64301 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq64151
       grind)
    | exact superpose eq64151 eq25
    | exact resolve eq25 eq64151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq64151
  have eq64383 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq64301
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64301
    | exact resolve eq64301 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq64301
  have eq64389 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq64383 eq27
    | exact resolve eq27 eq64383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq64383
  have eq64951 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq64389 eq84
    | exact resolve eq84 eq64389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq64389
  have eq65092 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq64951
       have i₂ := eq64300
       grind)
    | exact superpose eq64300 eq64951
    | exact resolve eq64951 eq64300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64300 eq64951
  have eq65109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65092 eq15
    | exact resolve eq15 eq65092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65092
  have eq65154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq65109
    | exact resolve eq65109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq65109
  have eq65163 : False := by grind
  exact eq65163

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_y_pxy_pyy_pyx_Equation1590 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1590 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  have eq51 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq44
    | exact resolve eq44 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq109 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq113 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq109
    | exact resolve eq109 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq115 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq113
    | exact resolve eq113 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq108
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq117
    | exact resolve eq117 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq123
    | exact resolve eq123 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq124
    | exact resolve eq124 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq144 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq141
    | exact resolve eq141 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq146 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq67 sF0
       grind)
    | exact superpose eq67 eq144
    | exact resolve eq144 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq153 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq16
    | exact resolve eq16 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op (M.op (M.op x y) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op x X0)) (M.op (M.op x y) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) X0)) (M.op (M.op (σ x) (σ y)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 (M.op x y)) (M.op (M.op x X0) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ x) X0) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq431 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq245 (M.op sF0 (M.op y X0))
       have i₂ := eq14 X0 y sF0
       grind)
    | exact superpose eq14 eq245
    | exact resolve eq245 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : y = (M.op (M.op x (M.op y (M.op x y))) (M.op x (M.op x y))) := by
    first
    | exact superpose eq245 eq54
    | exact resolve eq54 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq252 (M.op sF4 (M.op sF3 X0))
       have i₂ := eq14 X0 sF3 sF4
       grind)
    | exact superpose eq14 eq252
    | exact resolve eq252 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : (σ y) = (M.op (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq252 eq55
    | exact resolve eq55 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op (M.op X2 (M.op X1 X0)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X3 (M.op X2 (M.op X1 X0)) (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op y (M.op x X0)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq51 eq57
    | exact resolve eq57 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (M.op (σ y) (M.op (σ x) X0)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq52 eq57
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X0 X2)))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X3 (M.op X2 (M.op X0 X2)) X1
       have i₂ := eq57 (M.op X1 (M.op X2 (M.op X0 X2))) X2 X0
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X2) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op (M.op X1 X2) (M.op X2 X0)) X2 X1
       have i₂ := eq14 X0 X2 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X2 (M.op X0 X2))) ∨ (M.op X0 X1) = (k (M.op X2 (M.op X0 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X2 X1)) X0
       have i₂ := eq57 X0 X1 X2
       grind)
    | exact superpose eq57 eq13
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X2 (M.op X0 X2))) ∨ (M.op X1 (M.op X2 (M.op X0 X2))) = (k X1 (M.op X2 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X2 (M.op X0 X2))
       have i₂ := eq57 X1 X2 X0
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 X1 (M.op X2 (M.op X0 X2))
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X3 (M.op X0 X3))) (M.op X0 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X3 (M.op X0 X3))
       have i₂ := eq57 (M.op X1 X2) X3 X0
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 X1 : G, y = (M.op (M.op x (M.op X1 (M.op X0 X1))) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X1 (M.op x X1))
       have i₂ := eq57 sF0 X1 x
       grind)
    | exact superpose eq57 eq54
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq478 eq57
    | exact resolve eq57 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X3 X2) X1)) (M.op X0 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X1 (M.op X3 X2) (M.op X2 (M.op X3 X0)) X4
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X3 X2 (M.op X2 (M.op X3 X0))
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X1 (M.op (σ x) X0)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X0 X1 X2
       have i₂ := eq57 (M.op (M.op X0 X1) X2) X1 X0
       grind)
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq632 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq479 eq57
    | exact resolve eq57 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 : G, (M.op (M.op y (M.op x y)) (M.op (M.op x y) X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq244 eq56
    | exact resolve eq56 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ y) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq251 eq56
    | exact resolve eq56 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X1)) = (M.op (M.op x X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq245 eq56
    | exact resolve eq56 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1)) = (M.op (M.op (σ x) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq252 eq56
    | exact resolve eq56 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y (M.op (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X2 X1) (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op X3 (M.op X4 X0)) X2 X1 (M.op X4 X3)
       have i₂ := eq14 X0 X4 X3
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) x) (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 y X1 X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y X1 X0 x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op y (M.op x X0)))) = (M.op (M.op (M.op X2 X1) (M.op x y)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) X1 X0 (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) (M.op (σ x) X0)))) = (M.op (M.op (M.op X2 X1) (M.op (σ x) (σ y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 X1 X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq57 (M.op (M.op X0 (M.op X1 X2)) X3) (M.op X1 X2) X0
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ y) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq252 eq673
    | exact resolve eq673 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq727 : ∀ X0 X1 : G, (M.op x (M.op (M.op x y) X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq245 eq670
    | exact resolve eq670 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq805 : (M.op (M.op y x) (M.op x y)) = (M.op x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq478 eq431
    | exact resolve eq431 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1248 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq78
  have eq1256 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq350 X0 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq350
    | exact resolve eq350 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq350
  have eq1290 : ∀ X0 : G, (τ (k X0 (M.op (σ x) (σ x)))) = (k (τ X0) (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1256 X0
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq1256
    | exact resolve eq1256 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1293 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq1290 X0
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq1290
    | exact resolve eq1290 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1365 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq1248 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq1248 X0 X1
       grind)
    | exact superpose eq1248 eq13
    | (have j1 := eq1248 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq1248 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq1248 X0 X1
       grind)
    | exact resolve eq13 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1374 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1365 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1379 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq1374
    | (have j0 := eq1374 X0 X1
       grind)
    | exact resolve eq1374 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1380 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq1713 : ∀ X0 X1 : G, (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X0 X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq479 eq477
    | exact resolve eq477 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1747 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq251 eq477
    | exact resolve eq477 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1763 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) (M.op X1 X2) X1
       have i₂ := eq477 X0 X1 X2
       grind)
    | exact superpose eq477 eq14
    | exact resolve eq14 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1815 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X2 (M.op X0 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq586 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X3
       have i₂ := eq586 X1 X2 X0
       grind)
    | exact superpose eq586 eq586
    | exact resolve eq586 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1905 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X0)) = (M.op X1 (M.op (M.op X1 x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 (M.op (M.op X1 x) X0))
       have i₂ := eq586 X1 x X0
       grind)
    | exact superpose eq586 eq51
    | exact resolve eq51 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1912 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op X1 (M.op (M.op X1 (σ x)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 (M.op (M.op X0 sF2) x))
       have i₂ := eq586 X0 sF2 x
       grind)
    | exact superpose eq586 eq52
    | exact resolve eq52 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1991 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op X0 x) (M.op x y)))) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq478 eq246
    | exact resolve eq246 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1992 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))))) = (M.op (M.op (M.op x y) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq479 eq246
    | exact resolve eq246 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq2132 : ∀ X0 : G, (M.op (M.op (M.op x x) (M.op x y)) (M.op (M.op y y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq478 eq247
    | exact resolve eq247 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2277 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (M.op X0 x) (M.op x y)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) y) := by
    intro X0
    first
    | exact superpose eq478 eq253
    | exact resolve eq253 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2298 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq55 eq253
    | exact resolve eq253 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq2652 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq54 eq271
    | exact resolve eq271 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq3087 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq55 eq277
    | exact resolve eq277 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq3384 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3087 (M.op sF4 x)
       have i₂ := eq1763 sF3 sF4 x
       grind)
    | exact superpose eq1763 eq3087
    | exact resolve eq3087 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3087
  have eq3415 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (M.op X1 (M.op X0 X1))) X2) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 (M.op X1 (M.op X2 X1)) X1
       have i₂ := eq57 sF4 X1 X2
       grind)
    | exact superpose eq57 eq467
    | exact resolve eq467 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3526 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X2) = (M.op (M.op (σ x) (M.op X1 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq467 eq3415
    | exact resolve eq3415 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq3415
  have eq5583 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ x))) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq579 eq52
    | exact resolve eq52 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq5747 : ∀ X0 : G, (M.op (M.op y (M.op x (M.op x y))) (M.op x X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq680 (M.op y (M.op x sF0)) x
       have i₂ := eq469 sF0 x
       grind)
    | exact superpose eq469 eq680
    | exact resolve eq680 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq5753 : (M.op y y) = (M.op x (M.op x (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq54 eq680
    | exact resolve eq680 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq5911 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq472 eq681
    | exact resolve eq681 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5919 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq55 eq681
    | exact resolve eq681 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7195 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (σ y))))) := by
    intro X0
    first
    | exact superpose eq3384 eq586
    | exact resolve eq586 eq3384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq3384
  have eq8415 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X2) = (M.op (M.op (M.op (σ x) (M.op X0 X1)) X1) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq252 eq464
    | exact resolve eq464 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8456 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X2) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq464 X2 X0 X1 (M.op X2 X3)
       have i₂ := eq56 X3 X1 (M.op X0 X2) X2
       grind)
    | exact superpose eq56 eq464
    | exact resolve eq464 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq8665 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X2) = (M.op (M.op X0 (σ x)) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq8415 x X0 x
       have i₂ := eq464 X0 x sF2 x
       grind)
    | exact superpose eq464 eq8415
    | exact resolve eq8415 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8415
  have eq8993 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op y (M.op x X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq247 eq476
    | exact resolve eq476 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq8994 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op (σ y) (M.op (σ x) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq254 eq476
    | exact resolve eq476 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq9053 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) (M.op X0 (M.op (σ y) X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq472 (M.op x (M.op sF3 x)) X1
       have i₂ := eq476 sF3 sF2 x (M.op x (M.op sF3 x))
       grind)
    | exact superpose eq476 eq472
    | exact resolve eq472 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq476
  have eq9918 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op (M.op (σ x) X0) X1))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq488
    | exact resolve eq488 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq488
  have eq11673 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op x (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq489 eq576
    | exact resolve eq576 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq11674 : (M.op (M.op x y) y) = (M.op x (M.op y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq441 eq576
    | exact resolve eq576 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq11686 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq457 eq576
    | exact resolve eq576 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq13834 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq706 X2 (M.op X2 X1) (M.op X1 X0) X3
       have i₂ := eq477 X0 X2 X1
       grind)
    | exact superpose eq477 eq706
    | exact resolve eq706 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24865 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op y (M.op x y))) (M.op x y)) X1) = (M.op x (M.op X0 (M.op y (M.op x X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq245 (M.op x (M.op y (M.op x X0)))
       have i₂ := eq699 X0 (M.op y sF0) x
       grind)
    | exact superpose eq699 eq245
    | exact resolve eq245 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25042 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) (M.op x y)) X1) = (M.op (M.op (M.op X0 (M.op y (M.op x y))) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24865 X0 X1
       have i₂ := eq699 X1 x X0
       grind)
    | exact superpose eq699 eq24865
    | exact resolve eq24865 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq24865
  have eq25189 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) (M.op x y)) X1) = (M.op (M.op y X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25042 x x
       have i₂ := eq464 sF0 y x x
       grind)
    | exact superpose eq464 eq25042
    | exact resolve eq25042 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq25042
  have eq25967 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1380 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1380
    | (have j0 := eq1380 y X0
       grind)
    | exact resolve eq1380 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1380
  have eq27851 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X3 X2) (M.op X0 X4))) = X4 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq561 X0 x X2 X3 X4
       have i₂ := eq576 (M.op X0 X4) x (M.op X2 (M.op X3 X0)) (M.op X3 X2)
       grind)
    | exact superpose eq576 eq561
    | exact resolve eq561 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq28620 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y X0)) (M.op x (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq245 eq27851
    | exact resolve eq27851 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28622 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (σ x) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq252 eq27851
    | exact resolve eq27851 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27851
  have eq41664 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq446 eq484
    | (have j0 := eq484 (σ y) (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq484 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41671 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq251 eq41664
    | exact resolve eq41664 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41664
  have eq71312 : (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (k x x) (M.op x x)) := by
    first
    | exact superpose eq50 eq1293
    | exact resolve eq1293 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1293
  have eq71346 : (k (M.op x x) (M.op x x)) = (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq71312
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71312
    | exact resolve eq71312 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71312
  have eq71352 : (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq71346
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq71346
    | exact resolve eq71346 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71346
  have eq71354 : (M.op (M.op x x) (M.op x x)) = (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq71352
       have i₂ := eq67 (M.op x x)
       grind)
    | exact superpose eq67 eq71352
    | exact resolve eq71352 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71352
  have eq71356 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq71354
       have i₂ := eq67 (M.op sF2 sF2)
       grind)
    | exact superpose eq67 eq71354
    | exact resolve eq71354 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71354
  have eq71358 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) := by
    first
    | exact superpose eq675 eq71356
    | exact resolve eq71356 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq71356
  have eq71359 : (M.op (M.op x y) (M.op y x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq71358
       have i₂ := eq674 x x
       grind)
    | exact superpose eq674 eq71358
    | exact resolve eq71358 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq71358
  have eq71360 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) = (σ (M.op (M.op x y) (M.op y x))) := by
    first
    | exact superpose eq71359 eq15
    | exact resolve eq15 eq71359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71359
  have eq72093 : (M.op x y) ≠ (M.op y x) ∨ (M.op x y) = (k x (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq431 eq485
    | exact resolve eq485 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72099 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq446 eq485
    | exact resolve eq485 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq485
  have eq72106 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq251 eq72099
    | exact resolve eq72099 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq72099
  have eq72110 : (M.op x y) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq244 eq72093
    | exact resolve eq72093 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq72093
  have eq257076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq125 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq257076
    | exact resolve eq257076 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257076
  have eq257088 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq257077
       have r₂ := eq28
       grind)
    | exact resolve eq257077 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257077
  have eq257092 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq257088
    | exact resolve eq257088 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257088
  have eq257098 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq257092 eq41671
    | (have r₁ := eq41671
       have r₂ := eq257092
       grind)
    | exact resolve eq41671 eq257092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41671 eq257092
  have eq257242 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq257098
  have eq258647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq257242 eq125
    | exact resolve eq125 eq257242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq257242
  have eq258656 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq258647
  have eq258659 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq258656
       have r₂ := eq28
       grind)
    | exact resolve eq258656 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258656
  have eq258663 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq258659 eq153
    | exact resolve eq153 eq258659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq258659
  have eq258970 : x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq29 eq258663
    | exact resolve eq258663 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258663
  have eq258971 : (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq258970
  have eq258996 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72110
       have i₂ := eq258971
       grind)
    | exact superpose eq258971 eq72110
    | (have r₁ := eq72110
       have r₂ := eq258971
       grind)
    | exact resolve eq72110 eq258971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72110
  have eq258997 : x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq431 x
       have i₂ := eq258971
       grind)
    | exact superpose eq258971 eq431
    | exact resolve eq431 eq258971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq258971
  have eq259138 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by grind
  clear eq258996
  have eq260542 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq259138
       grind)
    | exact superpose eq259138 eq45
    | exact resolve eq45 eq259138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq259138
  have eq260560 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq260542
    | exact resolve eq260542 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260542
  have eq261150 : (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq258997 eq5753
    | exact resolve eq5753 eq258997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5753 eq258997
  have eq262103 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq261150
       grind)
    | exact superpose eq261150 eq115
    | exact resolve eq115 eq261150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261150
  have eq262410 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq262103
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq262103
    | exact resolve eq262103 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262103
  have eq262519 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ x))))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq262410 eq7195
    | exact resolve eq7195 eq262410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262410
  have eq262783 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq702 eq262519
    | exact resolve eq262519 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq262519
  have eq262833 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq262783
       have i₂ := eq1763 sF2 sF4 sF3
       grind)
    | exact superpose eq1763 eq262783
    | exact resolve eq262783 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262783
  have eq262875 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq262833 eq72106
    | (have r₁ := eq72106
       have r₂ := eq262833
       grind)
    | exact resolve eq72106 eq262833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72106 eq262833
  have eq263018 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq262875
  have eq263112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq263018 eq260560
    | exact resolve eq260560 eq263018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260560 eq263018
  have eq263114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq263112
  have eq263116 : x = (M.op y y) := by
    first
    | (have r₁ := eq263114
       have r₂ := eq28
       grind)
    | exact resolve eq263114 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263114
  have eq263119 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq263116
       grind)
    | exact superpose eq263116 eq115
    | exact resolve eq115 eq263116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq263288 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq1763 X0 y y
       have i₂ := eq263116
       grind)
    | exact superpose eq263116 eq1763
    | exact resolve eq1763 eq263116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263298 : y = (M.op (M.op (M.op x y) x) (M.op x x)) := by
    first
    | (have i₁ := eq28620 y y
       have i₂ := eq263116
       grind)
    | exact superpose eq263116 eq28620
    | exact resolve eq28620 eq263116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28620
  have eq263334 : y = (M.op y (M.op x x)) := by
    first
    | exact superpose eq506 eq263298
    | exact resolve eq263298 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq263298
  have eq263337 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq263288 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq263288
    | (have j0 := eq263288 X0
       grind)
    | exact resolve eq263288 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263288
  have eq263437 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq263119
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq263119
    | exact resolve eq263119 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263119
  have eq263905 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq263437 eq1763
    | exact resolve eq1763 eq263437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263916 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq263437 eq28622
    | exact resolve eq28622 eq263437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28622
  have eq263951 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq632 eq263916
    | exact resolve eq263916 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq263916
  have eq263954 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq27 eq263905
    | (have j0 := eq263905 X0
       grind)
    | exact resolve eq263905 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq263905
  have eq264907 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq263334
       grind)
    | exact superpose eq263334 eq51
    | exact resolve eq51 eq263334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq263334
  have eq265657 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) := by
    first
    | exact superpose eq263337 eq146
    | exact resolve eq146 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq273093 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq263951 eq52
    | exact resolve eq52 eq263951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq263951
  have eq277433 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op (M.op X0 x) y)) (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq11674 eq1815
    | exact resolve eq1815 eq11674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11674
  have eq277464 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (M.op X0 (σ x)) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq11686 eq1815
    | exact resolve eq1815 eq11686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11686
  have eq277555 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) X1)) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9053 (M.op sF2 x) (M.op x (M.op (M.op sF3 (M.op sF2 x)) x))
       have i₂ := eq1815 (M.op sF3 (M.op sF2 x)) sF2 x x
       grind)
    | exact superpose eq1815 eq9053
    | exact resolve eq9053 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq278096 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) X1)) X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq263954 eq277555
    | exact resolve eq277555 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277555
  have eq278173 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (M.op X0 (σ x)) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq273093 eq277464
    | exact resolve eq277464 eq273093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277464
  have eq278201 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op (M.op X0 x) y)) x) := by
    intro X0
    first
    | exact superpose eq264907 eq277433
    | exact resolve eq277433 eq264907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277433
  have eq279274 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq278096 X0 x
       have i₂ := eq576 X0 x sF3 sF2
       grind)
    | exact superpose eq576 eq278096
    | exact resolve eq278096 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq278096
  have eq279304 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) (σ x)) := by
    first
    | exact superpose eq1912 eq278173
    | exact resolve eq278173 eq1912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912 eq278173
  have eq279322 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) (M.op y y)) x) := by
    first
    | (have i₁ := eq278201 x
       have i₂ := eq1905 y x
       grind)
    | exact superpose eq1905 eq278201
    | exact resolve eq278201 eq1905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905 eq278201
  have eq279965 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ x)) := by
    first
    | exact superpose eq263954 eq279304
    | exact resolve eq279304 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279304
  have eq279974 : (M.op x (M.op x y)) = (M.op (M.op y (M.op y y)) x) := by
    first
    | exact superpose eq263337 eq279322
    | exact resolve eq279322 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279322
  have eq280341 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq279965
       have i₂ := eq57 sF2 sF3 sF3
       grind)
    | exact superpose eq57 eq279965
    | exact resolve eq279965 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279965
  have eq280345 : (M.op y x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq279974
       have i₂ := eq57 x y y
       grind)
    | exact superpose eq57 eq279974
    | exact resolve eq279974 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq279974
  have eq281235 : (M.op x (M.op y y)) = (M.op (M.op (M.op x (M.op x y)) x) (M.op x y)) := by
    first
    | (have i₁ := eq698 x y
       have i₂ := eq280345
       grind)
    | exact superpose eq280345 eq698
    | exact resolve eq698 eq280345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq281349 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq281235
       have i₂ := eq1763 sF0 x sF0
       grind)
    | exact superpose eq1763 eq281235
    | exact resolve eq281235 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763 eq281235
  have eq281441 : (M.op x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq281349
       have i₂ := eq263116
       grind)
    | exact superpose eq263116 eq281349
    | exact resolve eq281349 eq263116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281349
  have eq281501 : (M.op x x) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq263337 eq281441
    | exact resolve eq281441 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281441
  have eq292695 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op X0 x) (M.op x y)))) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | exact superpose eq263337 eq1991
    | exact resolve eq1991 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq292740 : (M.op (M.op y y) y) = (M.op y (M.op x (M.op x (M.op (M.op x y) y)))) := by
    first
    | exact superpose eq805 eq292695
    | exact resolve eq292695 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq292695
  have eq293079 : (M.op (M.op y y) y) = (M.op y (M.op x (M.op x x))) := by
    first
    | exact superpose eq264907 eq292740
    | exact resolve eq292740 eq264907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292740
  have eq293244 : (M.op x y) = (M.op y (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq293079
       have i₂ := eq263116
       grind)
    | exact superpose eq263116 eq293079
    | exact resolve eq293079 eq263116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263116 eq293079
  have eq293370 : (M.op x y) = (M.op y (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq293244
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq293244
    | exact resolve eq293244 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293244
  have eq293610 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))))) = (M.op (M.op y X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq263337 eq1992
    | exact resolve eq1992 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq293668 : (M.op y (σ y)) = (M.op (M.op y x) (σ y)) := by
    first
    | exact superpose eq479 eq293610
    | exact resolve eq293610 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq293610
  have eq293969 : (M.op y (σ y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq293668
       have i₂ := eq280345
       grind)
    | exact superpose eq280345 eq293668
    | exact resolve eq293668 eq280345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293668
  have eq296269 : ∀ X0 : G, (M.op (M.op y x) (M.op (M.op y y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq25189 eq2132
    | exact resolve eq2132 eq25189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132 eq25189
  have eq296270 : ∀ X0 : G, (M.op (M.op y x) (M.op (M.op y y) (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq263337 eq296269
    | exact resolve eq296269 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296269
  have eq296271 : ∀ X0 : G, (M.op (M.op y x) (M.op x (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq296270 X0
       have i₂ := eq727 X0 y
       grind)
    | exact superpose eq727 eq296270
    | exact resolve eq296270 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296270
  have eq296272 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq296271 X0
       have i₂ := eq727 (M.op sF0 X0) x
       grind)
    | exact superpose eq727 eq296271
    | exact resolve eq296271 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296271
  have eq296273 : ∀ X0 : G, (M.op x (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq263337 eq296272
    | exact resolve eq296272 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296272
  have eq296274 : ∀ X0 : G, (M.op x (M.op y (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq263337 eq296273
    | exact resolve eq296273 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296273
  have eq296278 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op x (M.op y (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq2652 eq296274
    | exact resolve eq296274 eq2652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652 eq296274
  have eq296755 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | exact superpose eq11673 eq296278
    | exact resolve eq296278 eq11673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296278
  have eq297800 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (M.op X0 x) (M.op x y)))) = (M.op (M.op (σ y) X0) y) := by
    intro X0
    first
    | exact superpose eq263954 eq2277
    | exact resolve eq2277 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277
  have eq297856 : (M.op (σ y) y) = (M.op (M.op (σ y) (σ x)) y) := by
    first
    | exact superpose eq478 eq297800
    | exact resolve eq297800 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq297800
  have eq298157 : (M.op (σ y) y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq280341 eq297856
    | exact resolve eq297856 eq280341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297856
  have eq300423 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) X0)) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq263954 eq2298
    | exact resolve eq2298 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298
  have eq300424 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq8994 eq300423
    | exact resolve eq300423 eq8994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300423
  have eq300513 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) X1) := by
    intro X0 X1
    first
    | exact superpose eq300424 eq9053
    | exact resolve eq9053 eq300424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9053 eq300424
  have eq300805 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq300513 X1 X1
       have i₂ := eq706 sF2 X1 sF4 (M.op (M.op X1 sF4) sF3)
       grind)
    | exact superpose eq706 eq300513
    | exact resolve eq300513 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300513
  have eq300960 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ y) (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) X1) := by
    intro X0 X1
    first
    | exact superpose eq263954 eq300805
    | exact resolve eq300805 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300805
  have eq301063 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) X1) := by
    intro X1
    first
    | exact superpose eq1747 eq300960
    | exact resolve eq300960 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747 eq300960
  have eq301131 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ y) (σ x)) X1) := by
    intro X1
    first
    | exact superpose eq8665 eq301063
    | exact resolve eq301063 eq8665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8665 eq301063
  have eq301174 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X1) := by
    intro X1
    first
    | exact superpose eq280341 eq301131
    | exact resolve eq301131 eq280341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301131
  have eq301203 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X1) := by
    intro X1
    first
    | exact superpose eq263954 eq301174
    | exact resolve eq301174 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301174
  have eq302941 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq281501 eq265657
    | exact resolve eq265657 eq281501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265657 eq281501
  have eq302942 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq302941
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq302941
    | exact resolve eq302941 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq302941
  have eq317482 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op (σ x) (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ y) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq5919 eq3526
    | exact resolve eq3526 eq5919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526 eq5919
  have eq319058 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) X0) := by
    intro X0
    first
    | (have i₁ := eq317482 X0
       have i₂ := eq706 sF2 sF4 sF4 (M.op sF3 sF3)
       grind)
    | exact superpose eq706 eq317482
    | exact resolve eq317482 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq317482
  have eq319724 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq263954 eq319058
    | exact resolve eq319058 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319058
  have eq320158 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq263954 eq319724
    | exact resolve eq319724 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319724
  have eq320421 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op (σ y) (M.op (σ y) (σ x))) X0) := by
    intro X0
    first
    | exact superpose eq263437 eq320158
    | exact resolve eq320158 eq263437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320158
  have eq320591 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq280341 eq320421
    | exact resolve eq320421 eq280341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320421
  have eq320699 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq302942 eq320591
    | exact resolve eq320591 eq302942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320591
  have eq320772 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq8994 eq320699
    | exact resolve eq320699 eq8994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320699
  have eq320813 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq263954 eq320772
    | exact resolve eq320772 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320772
  have eq320841 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq252 eq320813
    | exact resolve eq320813 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320813
  have eq325019 : ∀ X0 : G, (M.op (M.op y (σ y)) (M.op (σ y) (M.op (M.op x (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq293969 eq14
    | exact resolve eq14 eq293969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293969
  have eq325265 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op (M.op x (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq325019 X0
       have i₂ := eq727 (M.op (M.op x sF0) X0) sF3
       grind)
    | exact superpose eq727 eq325019
    | exact resolve eq325019 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq325019
  have eq325378 : ∀ X0 : G, (M.op x (M.op y (M.op (M.op x (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq263337 eq325265
    | exact resolve eq325265 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325265
  have eq325462 : ∀ X0 : G, (M.op x (M.op x (M.op x X0))) = X0 := by
    intro X0
    first
    | exact superpose eq680 eq325378
    | exact resolve eq325378 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq325378
  have eq330855 : ∀ X0 : G, (M.op (M.op (σ y) y) (M.op y (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq298157 eq14
    | exact resolve eq14 eq298157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298157
  have eq331101 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq726 eq330855
    | exact resolve eq330855 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq330855
  have eq331213 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq263954 eq331101
    | exact resolve eq331101 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331101
  have eq331296 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq681 eq331213
    | exact resolve eq331213 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq331213
  have eq342247 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq320841 eq477
    | exact resolve eq477 eq320841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq320841
  have eq346928 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x (M.op x x)) y) := by
    first
    | (have i₁ := eq484 x y x
       have i₂ := eq293370
       grind)
    | exact superpose eq293370 eq484
    | (have j0 := eq484 x y x
       grind)
    | (have r₁ := eq484 x y x
       have r₂ := eq293370
       grind)
    | exact resolve eq484 eq293370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq347220 : (M.op x y) = (k (M.op x (M.op x x)) y) := by
    first
    | (have r₁ := eq346928
       have r₂ := eq19
       grind)
    | exact resolve eq346928 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346928
  have eq347357 : (M.op x y) = (k (M.op x (M.op x x)) y) := by
    first
    | (have i₁ := eq347220
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq347220
    | exact resolve eq347220 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347220
  have eq354675 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ x))) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq263954 eq5583
    | exact resolve eq5583 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5583
  have eq354676 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))) = (M.op (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ y)) := by
    intro X0
    first
    | exact superpose eq302942 eq354675
    | exact resolve eq354675 eq302942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302942 eq354675
  have eq354770 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))))) (σ y)) := by
    first
    | exact superpose eq354676 eq9918
    | exact resolve eq9918 eq354676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9918 eq354676
  have eq355096 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) (M.op (σ y) (σ y))))) := by
    first
    | (have i₁ := eq354770
       have i₂ := eq691 sF3 sF1 sF1 (M.op sF3 (M.op sF3 (M.op sF2 sF4))) sF3
       grind)
    | exact superpose eq691 eq354770
    | exact resolve eq354770 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq354770
  have eq355269 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) (σ x)))) := by
    first
    | exact superpose eq263437 eq355096
    | exact resolve eq355096 eq263437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263437 eq355096
  have eq355343 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ x)))) := by
    first
    | exact superpose eq279274 eq355269
    | exact resolve eq355269 eq279274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279274 eq355269
  have eq355379 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ y) (σ x)))) := by
    first
    | exact superpose eq263954 eq355343
    | exact resolve eq355343 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355343
  have eq355402 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq280341 eq355379
    | exact resolve eq355379 eq280341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355379
  have eq355545 : (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq355402 eq1713
    | exact resolve eq1713 eq355402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713 eq355402
  have eq355626 : (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq701 eq355545
    | exact resolve eq355545 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq355545
  have eq355740 : (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq301203 eq355626
    | exact resolve eq355626 eq301203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301203 eq355626
  have eq355822 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq273093 eq355740
    | exact resolve eq355740 eq273093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273093 eq355740
  have eq357703 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op y (M.op x (M.op x y))) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq263337 eq5747
    | exact resolve eq5747 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5747
  have eq357704 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq357703 X0
       have i₂ := eq8993 sF0 (M.op x X0)
       grind)
    | exact superpose eq8993 eq357703
    | exact resolve eq357703 eq8993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8993 eq357703
  have eq357705 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op x X0)) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq263337 eq357704
    | exact resolve eq357704 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357704
  have eq357706 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq245 eq357705
    | exact resolve eq357705 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq357705
  have eq362135 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq263954 eq5911
    | exact resolve eq5911 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5911
  have eq362136 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq8994 eq362135
    | exact resolve eq362135 eq8994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8994 eq362135
  have eq362137 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq263954 eq362136
    | exact resolve eq362136 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362136
  have eq362138 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq252 eq362137
    | exact resolve eq362137 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq362137
  have eq391033 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ x)))) := by
    first
    | exact superpose eq355822 eq7195
    | exact resolve eq7195 eq355822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7195 eq355822
  have eq391380 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ (M.op x y)) (σ x)))) := by
    first
    | exact superpose eq263954 eq391033
    | exact resolve eq391033 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391033
  have eq520523 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) = (σ (k (M.op (M.op x y) (M.op y x)) y)) ∨ (σ y) = (σ (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x)))) := by
    first
    | exact superpose eq71360 eq25967
    | (have j0 := eq25967 (M.op (M.op x y) (M.op y x))
       grind)
    | exact resolve eq25967 eq71360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25967 eq71360
  have eq520929 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) = (σ (k (M.op y (M.op y x)) y)) ∨ (σ y) = (σ (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x)))) := by
    first
    | exact superpose eq263337 eq520523
    | exact resolve eq520523 eq263337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263337 eq520523
  have eq521031 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) = (σ (k (M.op x (M.op x x)) y)) ∨ (σ y) = (σ (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x)))) := by
    first
    | (have i₁ := eq520929
       have i₂ := eq357706 x
       grind)
    | exact superpose eq357706 eq520929
    | exact resolve eq520929 eq357706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357706 eq520929
  have eq521103 : (σ (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) ∨ (σ y) = (σ (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x)))) := by
    first
    | (have i₁ := eq521031
       have i₂ := eq347357
       grind)
    | exact superpose eq347357 eq521031
    | exact resolve eq521031 eq347357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347357 eq521031
  have eq521150 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ x)))) ∨ (σ y) = (σ (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x)))) := by
    first
    | exact superpose eq263954 eq521103
    | exact resolve eq521103 eq263954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263954 eq521103
  have eq521172 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ (σ y) = (σ (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x)))) := by
    first
    | exact superpose eq362138 eq521150
    | exact resolve eq521150 eq362138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362138 eq521150
  have eq521190 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ y) = (σ (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x)))) := by
    first
    | exact superpose eq280341 eq521172
    | exact resolve eq521172 eq280341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280341 eq521172
  have eq521202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x)))) := by
    first
    | exact superpose eq331296 eq521190
    | exact resolve eq521190 eq331296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331296 eq521190
  have eq521210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x)))) := by
    first
    | exact superpose eq21 eq521202
    | exact resolve eq521202 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521202
  have eq521218 : (σ y) = (σ (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x)))) := by
    first
    | (have r₁ := eq521210
       have r₂ := eq28
       grind)
    | exact resolve eq521210 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521210
  have eq521224 : (σ y) = (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y x) (M.op y x)))) := by
    first
    | (have i₁ := eq521218
       have i₂ := eq8456 sF0 (M.op y x) sF0 (M.op y x)
       grind)
    | (have i₁ := eq521218
       have i₂ := eq8456 sF0 sF0 (M.op y x) (M.op y x)
       grind)
    | exact superpose eq8456 eq521218
    | exact resolve eq521218 eq8456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8456 eq521218
  have eq521229 : (σ y) = (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op x y)) (M.op x (M.op x y))))) := by
    first
    | (have i₁ := eq521224
       have i₂ := eq280345
       grind)
    | exact superpose eq280345 eq521224
    | exact resolve eq521224 eq280345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280345 eq521224
  have eq521233 : (σ y) = (σ (M.op x (M.op (M.op x y) (M.op x (M.op x y))))) := by
    first
    | (have i₁ := eq521229
       have i₂ := eq13834 sF0 sF0 x (M.op x sF0)
       grind)
    | exact superpose eq13834 eq521229
    | exact resolve eq521229 eq13834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13834 eq521229
  have eq521236 : (σ y) = (σ (M.op (M.op x (M.op x y)) y)) := by
    first
    | exact superpose eq11673 eq521233
    | exact resolve eq521233 eq11673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11673 eq521233
  have eq521239 : (σ y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq296755 eq521236
    | exact resolve eq521236 eq296755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296755 eq521236
  have eq521240 : (σ y) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq521239
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq521239
    | exact resolve eq521239 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq521239
  have eq521241 : (σ x) = (σ y) := by
    first
    | exact superpose eq264907 eq521240
    | exact resolve eq521240 eq264907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264907 eq521240
  have eq521242 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq521241
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq521241
    | exact resolve eq521241 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521241
  have eq521244 : y = (τ (σ x)) := by
    first
    | exact superpose eq521242 eq30
    | exact resolve eq30 eq521242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq521479 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ (M.op x y)) (σ x)))) := by
    first
    | exact superpose eq521242 eq391380
    | exact resolve eq391380 eq521242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391380 eq521242
  have eq521524 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq342247 eq521479
    | exact resolve eq521479 eq342247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342247 eq521479
  have eq521707 : x = y := by
    first
    | exact superpose eq29 eq521244
    | exact resolve eq521244 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq521244
  have eq522043 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq521524 eq28
    | exact resolve eq28 eq521524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq521524
  have eq523720 : (M.op x y) = (M.op x (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq293370
       have i₂ := eq521707
       grind)
    | exact superpose eq521707 eq293370
    | exact resolve eq293370 eq521707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293370 eq521707
  have eq523801 : x = (M.op x y) := by
    first
    | (have i₁ := eq523720
       have i₂ := eq325462 x
       grind)
    | exact superpose eq325462 eq523720
    | exact resolve eq523720 eq325462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325462 eq523720
  have eq524378 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq523801 eq21
    | exact resolve eq21 eq523801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq523801
  have eq524811 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq524378
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq524378
    | exact resolve eq524378 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq524378
  have eq524984 : False := by grind
  exact eq524984
