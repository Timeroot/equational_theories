import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation124`: `x = y ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_x_pxy_Equation124 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law124 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law124.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) X0)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X1 (M.op X0 (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq19
  have eq26 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq18
    | exact resolve eq18 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq76 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq61 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq157 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq61
    | (have j1 := eq39 X1 X0
       grind)
    | exact resolve eq61 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq169 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq157 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq251 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq33
  have eq267 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq251 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq251
    | exact resolve eq251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq452 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq79 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact superpose eq79 eq26
    | (have j1 := eq79 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact resolve eq26 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq454 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq267 X0
       have i₂ := eq79 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact superpose eq79 eq267
    | (have j1 := eq79 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq267 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq267
  have eq465 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq454 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq466 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq452 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq537 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op X0 (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq9 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq465 X0
       grind)
    | exact superpose eq465 eq9
    | exact resolve eq9 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq537 X0
       have i₂ := eq465 X0
       grind)
    | exact superpose eq465 eq537
    | exact resolve eq537 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq537
  have eq640 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq466 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq466
    | exact resolve eq466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq667 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38
    | exact resolve eq38 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq738 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq667 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq667
    | (have j0 := eq667 X0 X1
       grind)
    | exact resolve eq667 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq820 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq541 X0
       grind)
    | exact superpose eq541 eq11
    | exact resolve eq11 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6289 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1
       have i₂ := eq738 X0 X1
       grind)
    | (have i₁ := eq61 X0
       have i₂ := eq738 (M.op X0 X0) X1
       grind)
    | exact superpose eq738 eq61
    | (have j1 := eq738 X0 X1
       grind)
    | exact resolve eq61 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq738
  have eq6342 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289
  have eq192381 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 y x
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 y x
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq199228 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq192381
       have i₂ := eq6342 y x
       grind)
    | exact superpose eq6342 eq192381
    | (have j1 := eq6342 (σ y) (σ x)
       grind)
    | (have r₁ := eq192381
       have r₂ := eq6342 y x
       grind)
    | exact resolve eq192381 eq6342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6342 eq192381
  have eq199231 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq199228
  have eq200723 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq199231
       grind)
    | exact superpose eq199231 eq9
    | exact resolve eq9 eq199231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204451 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq200723
       have i₂ := eq199231
       grind)
    | exact superpose eq199231 eq200723
    | exact resolve eq200723 eq199231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199231 eq200723
  have eq204469 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq204451
  have eq204478 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq204469
       have i₂ := eq820 x
       grind)
    | exact superpose eq820 eq204469
    | exact resolve eq204469 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq204469
  have eq204913 : (τ (M.op (σ y) (σ y))) = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq541 (M.op x x)
       have i₂ := eq204478
       grind)
    | exact superpose eq204478 eq541
    | exact resolve eq541 eq204478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204478
  have eq204955 : x = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq204913
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq204913
    | exact resolve eq204913 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq204913
  have eq204986 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq204955
       have i₂ := eq541 y
       grind)
    | exact superpose eq541 eq204955
    | exact resolve eq204955 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq204955
  have eq206420 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq204986
       grind)
    | exact superpose eq204986 eq56
    | exact resolve eq56 eq204986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq204986
  have eq206489 : x = (M.op x y) := by grind
  clear eq206420
  have eq206967 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq206489
       grind)
    | exact superpose eq206489 eq9
    | exact resolve eq9 eq206489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206987 : y = (M.op x x) := by
    first
    | (have i₁ := eq206967
       have i₂ := eq206489
       grind)
    | exact superpose eq206489 eq206967
    | exact resolve eq206967 eq206489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206967
  have eq208894 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq640 x
       have i₂ := eq206987
       grind)
    | exact superpose eq206987 eq640
    | exact resolve eq640 eq206987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq206987
  have eq217469 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq208894
       grind)
    | exact superpose eq208894 eq16
    | exact resolve eq16 eq208894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208894
  have eq217494 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq217469
       have i₂ := eq206489
       grind)
    | exact superpose eq206489 eq217469
    | exact resolve eq217469 eq206489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206489 eq217469
  have eq217495 : False := by grind
  exact eq217495

/-- `Equation124`: `x = y ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_y_pxy_Equation124 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law124 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law124.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) X0)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X1 (M.op X0 (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq19
  have eq26 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq18
    | exact resolve eq18 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq76 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq61 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq157 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq61
    | (have j1 := eq39 X1 X0
       grind)
    | exact resolve eq61 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq169 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq157 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq251 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq33
  have eq267 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq251 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq251
    | exact resolve eq251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq452 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq79 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact superpose eq79 eq26
    | (have j1 := eq79 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact resolve eq26 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq454 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq267 X0
       have i₂ := eq79 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact superpose eq79 eq267
    | (have j1 := eq79 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq267 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq267
  have eq465 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq454 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq466 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq452 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq537 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op X0 (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq9 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq465 X0
       grind)
    | exact superpose eq465 eq9
    | exact resolve eq9 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq537 X0
       have i₂ := eq465 X0
       grind)
    | exact superpose eq465 eq537
    | exact resolve eq537 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq537
  have eq641 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq466 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq466
    | exact resolve eq466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq669 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38
    | exact resolve eq38 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq740 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq822 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq541 X0
       grind)
    | exact superpose eq541 eq11
    | exact resolve eq11 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6300 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1
       have i₂ := eq740 X0 X1
       grind)
    | (have i₁ := eq61 X0
       have i₂ := eq740 (M.op X0 X0) X1
       grind)
    | exact superpose eq740 eq61
    | (have j1 := eq740 X0 X1
       grind)
    | exact resolve eq61 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq740
  have eq6353 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300
  have eq200740 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 y x
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 y x
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq209579 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq200740
       have i₂ := eq6353 y x
       grind)
    | exact superpose eq6353 eq200740
    | (have j1 := eq6353 (σ y) (σ x)
       grind)
    | (have r₁ := eq200740
       have r₂ := eq6353 y x
       grind)
    | exact resolve eq200740 eq6353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6353 eq200740
  have eq209582 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq209579
  have eq210975 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq209582
       grind)
    | exact superpose eq209582 eq9
    | exact resolve eq9 eq209582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212242 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq210975
       have i₂ := eq209582
       grind)
    | exact superpose eq209582 eq210975
    | exact resolve eq210975 eq209582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209582 eq210975
  have eq212259 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq212242
  have eq212267 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212259
       have i₂ := eq822 x
       grind)
    | exact superpose eq822 eq212259
    | exact resolve eq212259 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq212259
  have eq212867 : (τ (M.op (σ y) (σ y))) = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq541 (M.op x x)
       have i₂ := eq212267
       grind)
    | exact superpose eq212267 eq541
    | exact resolve eq541 eq212267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212267
  have eq212909 : x = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212867
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq212867
    | exact resolve eq212867 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq212867
  have eq212940 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212909
       have i₂ := eq541 y
       grind)
    | exact superpose eq541 eq212909
    | exact resolve eq212909 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq212909
  have eq215320 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq212940
       grind)
    | exact superpose eq212940 eq56
    | exact resolve eq56 eq212940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq212940
  have eq215388 : x = (M.op x y) := by grind
  clear eq215320
  have eq216759 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq215388
       grind)
    | exact superpose eq215388 eq9
    | exact resolve eq9 eq215388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216777 : y = (M.op x x) := by
    first
    | (have i₁ := eq216759
       have i₂ := eq215388
       grind)
    | exact superpose eq215388 eq216759
    | exact resolve eq216759 eq215388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216759
  have eq217349 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq641 x
       have i₂ := eq216777
       grind)
    | exact superpose eq216777 eq641
    | exact resolve eq641 eq216777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq216777
  have eq225552 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq217349
       grind)
    | exact superpose eq217349 eq16
    | exact resolve eq16 eq217349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217349
  have eq225577 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq225552
       have i₂ := eq215388
       grind)
    | exact superpose eq215388 eq225552
    | exact resolve eq225552 eq215388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215388 eq225552
  have eq225578 : False := by grind
  exact eq225578

/-- `Equation124`: `x = y ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_y_pxy_Equation124 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law124 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law124.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) X0)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X1 (M.op X0 (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq23 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq25
    | exact resolve eq25 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq18
    | exact resolve eq18 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq61 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq127 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq131 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (M.op (σ (k X0 X1)) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ X0)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq9
    | (have j1 := eq39 X0 X1
       grind)
    | exact resolve eq9 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X2) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X2
       have i₂ := eq39 X0 X2
       grind)
    | exact superpose eq39 eq15
    | (have j1 := eq39 X0 X2
       grind)
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq152 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq165 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq152 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq152
    | (have j0 := eq152 X0
       grind)
    | exact resolve eq152 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq222 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq26 (τ X0)
       grind)
    | exact superpose eq26 eq19
    | exact resolve eq19 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq222 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq222
    | exact resolve eq222 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq247 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq33
  have eq263 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq247 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq247
    | exact resolve eq247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq621 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq165 (τ X0)
       grind)
    | exact superpose eq165 eq19
    | (have j1 := eq165 (τ X0)
       grind)
    | exact resolve eq19 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq655 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq621 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq621
    | (have j0 := eq621 X0
       grind)
    | exact resolve eq621 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq662 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq655 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq655
    | (have j0 := eq655 X0
       grind)
    | exact resolve eq655 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq665 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq662 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq662
    | (have j0 := eq662 X0
       grind)
    | exact resolve eq662 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq695 : ∀ X0 : G, (k X0 (σ (k (σ (τ (τ X0))) (τ X0)))) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq223 X0
       have i₂ := eq38 (τ (τ X0)) (τ X0)
       grind)
    | exact superpose eq38 eq223
    | (have j1 := eq38 (τ (τ X0)) (τ X0)
       grind)
    | exact resolve eq223 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq749 : ∀ X0 : G, (k X0 (σ (k (σ (τ (τ X0))) (τ X0)))) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq766 : ∀ X0 : G, (k X0 (k (σ (σ (τ (τ X0)))) X0)) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq749 X0
       have i₂ := eq20 X0 (σ (τ (τ X0)))
       grind)
    | exact superpose eq20 eq749
    | (have j0 := eq749 X0
       grind)
    | exact resolve eq749 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq781 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq766 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq766
    | (have j0 := eq766 X0
       grind)
    | exact resolve eq766 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq786 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq781 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq781
    | (have j0 := eq781 X0
       grind)
    | exact resolve eq781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq2191 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X0)) (M.op (σ (τ (k X0 X1))) (σ (τ X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq131 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq131
    | (have j0 := eq131 (τ X0) (τ X1)
       grind)
    | exact resolve eq131 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq2231 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op (σ (τ (k X0 X1))) X1)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2191 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2191
    | (have j0 := eq2191 X0 X1
       grind)
    | exact resolve eq2191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191
  have eq2238 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op (k X0 X1) X1)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2231 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2231
    | (have j0 := eq2231 X0 X1
       grind)
    | exact resolve eq2231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2242 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X1) X1)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2238 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2238
    | (have j0 := eq2238 X0 X1
       grind)
    | exact resolve eq2238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq2244 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 (M.op (k X0 X1) X1)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2242 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2242
    | (have j0 := eq2242 X0 X1
       grind)
    | exact resolve eq2242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq2245 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 (M.op (k X0 X1) X1)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2244 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2244
    | (have j0 := eq2244 X0 X1
       grind)
    | exact resolve eq2244 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq2246 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 (M.op (k X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2245 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2245
    | (have j0 := eq2245 X0 X1
       grind)
    | exact resolve eq2245 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq2247 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X1) X1)) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2246 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2246
    | (have j0 := eq2246 X0 X1
       grind)
    | exact resolve eq2246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246
  have eq3662 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k X2 (τ X0))) = (k (σ X2) (M.op (σ X1) (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134
    | (have j0 := eq134 X1 X2 (τ X0)
       grind)
    | exact resolve eq134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq3777 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X2 (τ X0))) = (k (σ X2) (M.op (σ X1) (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3662 X0 X1 X2
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq3662
    | (have j0 := eq3662 X0 X1 X2
       grind)
    | exact resolve eq3662 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq3796 : ∀ X0 X1 X2 : G, (k (σ X2) X0) = (k (σ X2) (M.op (σ X1) (σ X1))) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3777 X0 X1 X2
       have i₂ := eq20 X0 X2
       grind)
    | exact superpose eq20 eq3777
    | (have j0 := eq3777 X0 X1 X2
       grind)
    | exact resolve eq3777 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq9139 : ∀ X0 : G, (k X0 (σ (σ (τ (τ X0))))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq223 X0
       have i₂ := eq786 X0
       grind)
    | exact superpose eq786 eq223
    | (have j1 := eq786 X0
       grind)
    | exact resolve eq223 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq9151 : ∀ X0 : G, (τ (τ X0)) = (k (τ (τ X0)) (τ (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq93 (τ (τ X0))
       have i₂ := eq786 X0
       grind)
    | exact superpose eq786 eq93
    | (have j1 := eq786 X0
       grind)
    | exact resolve eq93 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq9168 : ∀ X0 : G, (τ (τ X0)) = (τ (k (τ X0) (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9151 X0
       have i₂ := eq44 (τ X0) (τ X0)
       grind)
    | exact superpose eq44 eq9151
    | (have j0 := eq9151 X0
       grind)
    | exact resolve eq9151 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9151
  have eq9174 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9139 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq9139
    | (have j0 := eq9139 X0
       grind)
    | exact resolve eq9139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9139
  have eq9206 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9168 X0
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq9168
    | (have j0 := eq9168 X0
       grind)
    | exact resolve eq9168 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9168
  have eq9211 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9174 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9174
    | (have j0 := eq9174 X0
       grind)
    | exact resolve eq9174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9174
  have eq11986 : ∀ X0 X1 : G, (τ (k X1 (τ (k X0 X0)))) = (k (τ X1) (τ (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44 (τ (k X0 X0)) X1
       have i₂ := eq9206 X0
       grind)
    | exact superpose eq9206 eq44
    | (have j1 := eq9206 X0
       grind)
    | exact resolve eq44 eq9206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11987 : ∀ X0 X1 : G, (τ (k (τ (k X0 X0)) X1)) = (k (τ (τ X0)) (τ X1)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 (τ (k X0 X0))
       have i₂ := eq9206 X0
       grind)
    | exact superpose eq9206 eq44
    | (have j1 := eq9206 X0
       grind)
    | exact resolve eq44 eq9206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9206
  have eq12071 : ∀ X0 X1 : G, (τ (k (τ X0) X1)) = (τ (k (τ (k X0 X0)) X1)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11987 X0 X1
       have i₂ := eq44 X1 (τ X0)
       grind)
    | exact superpose eq44 eq11987
    | (have j0 := eq11987 X0 X1
       grind)
    | exact resolve eq11987 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11987
  have eq12072 : ∀ X0 X1 : G, (τ (k X1 (τ (k X0 X0)))) = (τ (k X1 (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11986 X0 X1
       have i₂ := eq44 (τ X0) X1
       grind)
    | exact superpose eq44 eq11986
    | (have j0 := eq11986 X0 X1
       grind)
    | exact resolve eq11986 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11986
  have eq115786 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (k (σ X0) (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3796 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3796
  have eq115809 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    grind
  clear eq115786
  have eq116212 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq115809 X0 X1
       have j1 := eq74 X1 (σ X0)
       grind)
    | (have r₁ := eq115809 X0 X0
       have r₂ := eq74 X0 (σ X0)
       grind)
    | (have r₁ := eq115809 X0 (σ X0)
       have r₂ := eq74 (σ X0) (σ X0)
       grind)
    | exact resolve eq115809 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq115809
  have eq116842 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116212 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq116212
    | exact resolve eq116212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116998 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq116212 X0 (σ X1)
       grind)
    | exact superpose eq116212 eq15
    | (have j1 := eq116212 X0 (σ X1)
       grind)
    | exact resolve eq15 eq116212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116212
  have eq118271 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq116842 (τ X0) X1
       grind)
    | exact superpose eq116842 eq19
    | (have j1 := eq116842 (τ X0) X1
       grind)
    | exact resolve eq19 eq116842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq121603 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118271 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq118271
    | exact resolve eq118271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118271
  have eq121952 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq121603 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq121603
    | (have j0 := eq121603 X0 X1
       grind)
    | exact resolve eq121603 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121603
  have eq126082 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq116998 x y
       grind)
    | exact superpose eq116998 eq16
    | (have j1 := eq116998 x y
       grind)
    | exact resolve eq16 eq116998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126159 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq116998 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116998
  have eq127119 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq126159 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq126159
    | (have j0 := eq126159 (τ X0) (τ X1)
       grind)
    | exact resolve eq126159 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127279 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq127119 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq127119
    | (have j0 := eq127119 X0 X1
       grind)
    | exact resolve eq127119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127119
  have eq127320 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq127279 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq127279
    | (have j0 := eq127279 X0 X1
       grind)
    | exact resolve eq127279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127279
  have eq127347 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq127320 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq127320
    | (have j0 := eq127320 X0 X1
       grind)
    | exact resolve eq127320 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127320
  have eq127365 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq127347 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq127347
    | (have j0 := eq127347 X0 X1
       grind)
    | exact resolve eq127347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127347
  have eq128928 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127365 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq127365
    | (have j0 := eq127365 (τ X0) (τ X1)
       grind)
    | exact resolve eq127365 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134330 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq126082
       have i₂ := eq121952 x y
       grind)
    | exact superpose eq121952 eq126082
    | (have j1 := eq121952 (σ x) (σ y)
       grind)
    | (have r₁ := eq126082
       have r₂ := eq121952 x y
       grind)
    | exact resolve eq126082 eq121952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134337 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq134330
  have eq135708 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134337
       grind)
    | exact superpose eq134337 eq16
    | exact resolve eq16 eq134337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135712 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq134337
       grind)
    | exact superpose eq134337 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq134337
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq134337
       grind)
    | exact resolve eq13 eq134337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135713 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18 (σ y) (σ x)
       have i₂ := eq134337
       grind)
    | exact superpose eq134337 eq18
    | exact resolve eq18 eq134337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135731 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq135712
  have eq135737 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq135713
       have i₂ := eq61 (σ y)
       grind)
    | exact superpose eq61 eq135713
    | exact resolve eq135713 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135713
  have eq135738 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq135731
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq135731
    | exact resolve eq135731 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135731
  have eq138927 : y = (k y (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq263 y
       have i₂ := eq135737
       grind)
    | exact superpose eq135737 eq263
    | exact resolve eq263 eq135737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140649 : y = (k y (τ (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq138927
       have i₂ := eq134337
       grind)
    | exact superpose eq134337 eq138927
    | exact resolve eq138927 eq134337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134337 eq138927
  have eq140753 : y = (k y (τ (σ y))) ∨ y = (M.op x y) := by grind
  clear eq140649
  have eq140764 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq140753
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq140753
    | exact resolve eq140753 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140753
  have eq142580 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq126159 y y
       have i₂ := eq140764
       grind)
    | exact superpose eq140764 eq126159
    | (have j0 := eq126159 y y
       grind)
    | exact resolve eq126159 eq140764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142581 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq127365 y y
       have i₂ := eq140764
       grind)
    | exact superpose eq140764 eq127365
    | (have j0 := eq127365 y y
       grind)
    | (have r₁ := eq127365 y y
       have r₂ := eq140764
       grind)
    | exact resolve eq127365 eq140764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142582 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq128928 y y
       have i₂ := eq140764
       grind)
    | exact superpose eq140764 eq128928
    | (have j0 := eq128928 y y
       grind)
    | exact resolve eq128928 eq140764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128928 eq140764
  have eq142583 : (τ y) = (M.op (τ y) (τ y)) ∨ y = (M.op x y) := by grind
  clear eq142582
  have eq142584 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq142581
  have eq142585 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq142580
  have eq144350 : (τ y) = (k (τ y) (τ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93 (τ y)
       have i₂ := eq142583
       grind)
    | exact superpose eq142583 eq93
    | exact resolve eq93 eq142583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142583
  have eq144361 : (τ y) = (τ (k y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq144350
       have i₂ := eq44 y y
       grind)
    | exact superpose eq44 eq144350
    | exact resolve eq144350 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144350
  have eq145240 : ∀ X0 : G, (τ (k X0 (k y y))) = (k (τ X0) (τ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq44 (k y y) X0
       have i₂ := eq144361
       grind)
    | exact superpose eq144361 eq44
    | exact resolve eq44 eq144361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145241 : ∀ X0 : G, (τ (k (k y y) X0)) = (k (τ y) (τ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq44 X0 (k y y)
       have i₂ := eq144361
       grind)
    | exact superpose eq144361 eq44
    | exact resolve eq44 eq144361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144361
  have eq145334 : ∀ X0 : G, (τ (k y X0)) = (τ (k (k y y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq145241 X0
       have i₂ := eq44 X0 y
       grind)
    | exact superpose eq44 eq145241
    | exact resolve eq145241 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145241
  have eq145335 : ∀ X0 : G, (τ (k X0 y)) = (τ (k X0 (k y y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq145240 X0
       have i₂ := eq44 y X0
       grind)
    | exact superpose eq44 eq145240
    | exact resolve eq145240 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq145240
  have eq146209 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93 (σ y)
       have i₂ := eq142585
       grind)
    | exact superpose eq142585 eq93
    | exact resolve eq93 eq142585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq146225 : (σ y) = (σ (k y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq146209
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq146209
    | exact resolve eq146209 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146209
  have eq149568 : ∀ X0 : G, (k (k y y) X0) = (σ (τ (k y X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11 (k (k y y) X0)
       have i₂ := eq145334 X0
       grind)
    | exact superpose eq145334 eq11
    | exact resolve eq11 eq145334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145334
  have eq149643 : ∀ X0 : G, (k y X0) = (k (k y y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq149568 X0
       have i₂ := eq11 (k y X0)
       grind)
    | exact superpose eq11 eq149568
    | exact resolve eq149568 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149568
  have eq150079 : ∀ X0 : G, (k y X0) ≠ X0 ∨ (M.op (k y y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq127365 (k y y) X0
       have i₂ := eq149643 X0
       grind)
    | exact superpose eq149643 eq127365
    | (have j0 := eq127365 y X0
       grind)
    | exact resolve eq127365 eq149643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150096 : ∀ X0 : G, (k (σ (k y y)) X0) = (σ (k y (τ X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (k y y)
       have i₂ := eq149643 (τ X0)
       grind)
    | exact superpose eq149643 eq20
    | exact resolve eq20 eq149643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150160 : ∀ X0 : G, (k (σ y) X0) = (k (σ (k y y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq150096 X0
       have i₂ := eq20 X0 y
       grind)
    | exact superpose eq20 eq150096
    | exact resolve eq150096 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq150096
  have eq150454 : ∀ X0 : G, (k X0 (k y y)) = (σ (τ (k X0 y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (k y y))
       have i₂ := eq145335 X0
       grind)
    | exact superpose eq145335 eq11
    | exact resolve eq11 eq145335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145335
  have eq150535 : ∀ X0 : G, (k X0 y) = (k X0 (k y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq150454 X0
       have i₂ := eq11 (k X0 y)
       grind)
    | exact superpose eq11 eq150454
    | exact resolve eq150454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150454
  have eq151007 : (k y (k y y)) = (k (k y y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq149643 (k y y)
       have i₂ := eq150535 (k y y)
       grind)
    | exact superpose eq150535 eq149643
    | exact resolve eq149643 eq150535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151028 : (k y (k y y)) = (k (k y y) y) ∨ y = (M.op x y) := by grind
  clear eq151007
  have eq158841 : (σ y) ≠ (σ (k y (k y y))) ∨ (σ y) = (M.op (σ (k y y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq126159 (k y y) y
       have i₂ := eq151028
       grind)
    | exact superpose eq151028 eq126159
    | (have j0 := eq126159 (k y y) y
       grind)
    | exact resolve eq126159 eq151028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151028
  have eq164571 : y ≠ (M.op y y) ∨ (M.op y y) = (M.op (k y y) (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq150079
  have eq164587 : (M.op y y) = (M.op (k y y) (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq164571
       have r₂ := eq142584
       grind)
    | exact resolve eq164571 eq142584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142584 eq164571
  have eq166089 : (M.op y y) = (M.op (k y y) (M.op (M.op y y) (M.op y y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (M.op y y) (k y y)
       have i₂ := eq164587
       grind)
    | exact superpose eq164587 eq9
    | exact resolve eq9 eq164587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164587
  have eq166101 : (M.op y y) = (M.op (k y y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq166089
       have i₂ := eq65 y
       grind)
    | exact superpose eq65 eq166089
    | exact resolve eq166089 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166089
  have eq366880 : ∀ X0 X1 : G, (k (τ (k X0 X0)) X1) = (σ (τ (k (τ X0) X1))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (τ (k X0 X0)) X1)
       have i₂ := eq12071 X0 X1
       grind)
    | exact superpose eq12071 eq11
    | (have j1 := eq12071 X0 X1
       grind)
    | exact resolve eq11 eq12071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12071
  have eq366904 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ (k X0 X0)) X1) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq366880 X0 X1
       have i₂ := eq11 (k (τ X0) X1)
       grind)
    | exact superpose eq11 eq366880
    | (have j0 := eq366880 X0 X1
       grind)
    | exact resolve eq366880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366880
  have eq369548 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (k (τ (σ X0)) X1) = (k (τ (k (σ X0) (σ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0) (σ X0)
       have i₂ := eq366904 (σ X0) X1
       grind)
    | exact superpose eq366904 eq46
    | (have j1 := eq366904 (σ X0) X1
       grind)
    | exact resolve eq46 eq366904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366904
  have eq369571 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k (τ (σ X0)) X1) = (k (τ (k (σ X0) (σ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq369548 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq369548
    | (have j0 := eq369548 X0 X1
       grind)
    | exact resolve eq369548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369548
  have eq369603 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (k (k (τ (σ X0)) X0) X1) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq369571 X0 X1
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq369571
    | (have j0 := eq369571 X0 X1
       grind)
    | exact resolve eq369571 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369571
  have eq369622 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X0) X1) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq369603 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq369603
    | (have j0 := eq369603 X0 X1
       grind)
    | exact resolve eq369603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369603
  have eq370244 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op (k X0 X0) X1) = X1 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq127365 (k X0 X0) X1
       have i₂ := eq369622 X0 X1
       grind)
    | exact superpose eq369622 eq127365
    | (have j0 := eq127365 X0 X1
       have j1 := eq369622 X0 X1
       grind)
    | exact resolve eq127365 eq369622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127365 eq369622
  have eq380491 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (k X0 X0) (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    grind
  clear eq370244
  have eq380497 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq380491 X0
       have j1 := eq665 X0
       grind)
    | (have r₁ := eq380491 X0
       have r₂ := eq665 X0
       grind)
    | exact resolve eq380491 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq380491
  have eq380972 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq380497 (σ y)
       have i₂ := eq142585
       grind)
    | exact superpose eq142585 eq380497
    | (have j0 := eq380497 (σ y)
       grind)
    | exact resolve eq380497 eq142585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142585 eq380497
  have eq380988 : (σ y) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq380972
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq380972
    | exact resolve eq380972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380972
  have eq380994 : (σ y) = (σ (k y (k (τ (σ y)) y))) ∨ (σ y) = (M.op (σ (k y y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq380988
       have i₂ := eq23 (σ y) y y
       grind)
    | exact superpose eq23 eq380988
    | exact resolve eq380988 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq380988
  have eq380996 : (σ y) = (σ (k y (k y y))) ∨ (σ y) = (M.op (σ (k y y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq380994
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq380994
    | exact resolve eq380994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380994
  have eq380998 : (σ y) = (M.op (σ (k y y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq380996
       have r₂ := eq158841
       grind)
    | exact resolve eq380996 eq158841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158841 eq380996
  have eq382100 : (M.op (σ y) (σ y)) = (M.op (σ (k y y)) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18 (σ y) (σ (k y y))
       have i₂ := eq380998
       grind)
    | exact superpose eq380998 eq18
    | exact resolve eq18 eq380998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq380998
  have eq382114 : (M.op (σ y) (σ y)) = (M.op (σ (k y y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq382100
       have i₂ := eq61 (σ y)
       grind)
    | exact superpose eq61 eq382100
    | exact resolve eq382100 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382100
  have eq390946 : ∀ X0 X1 : G, (k X0 (τ (k X1 X1))) = (σ (τ (k X0 (τ X1)))) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (τ (k X1 X1)))
       have i₂ := eq12072 X1 X0
       grind)
    | exact superpose eq12072 eq11
    | (have j1 := eq12072 X1 X1
       grind)
    | exact resolve eq11 eq12072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12072
  have eq390970 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k X0 (τ (k X1 X1))) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq390946 X0 X1
       have i₂ := eq11 (k X0 (τ X1))
       grind)
    | exact superpose eq11 eq390946
    | (have j0 := eq390946 X0 X1
       grind)
    | exact resolve eq390946 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390946
  have eq393750 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (k X1 (τ (σ X0))) = (k X1 (τ (k (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0) (σ X0)
       have i₂ := eq390970 X1 (σ X0)
       grind)
    | exact superpose eq390970 eq46
    | (have j1 := eq390970 X1 (σ X0)
       grind)
    | exact resolve eq46 eq390970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq390970
  have eq393773 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k X1 (τ (σ X0))) = (k X1 (τ (k (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq393750 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq393750
    | (have j0 := eq393750 X0 X1
       grind)
    | exact resolve eq393750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393750
  have eq393801 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = (k X1 (k (τ (σ X0)) X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq393773 X0 X1
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq393773
    | (have j0 := eq393773 X0 X1
       grind)
    | exact resolve eq393773 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393773
  have eq393817 : ∀ X0 X1 : G, (k X1 X0) = (k X1 (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq393801 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq393801
    | (have j0 := eq393801 X0 X1
       grind)
    | exact resolve eq393801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393801
  have eq396754 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq393817 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393817
  have eq396767 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq396754 X0
       have j1 := eq9211 X0
       grind)
    | (have r₁ := eq396754 X0
       have r₂ := eq9211 X0
       grind)
    | exact resolve eq396754 eq9211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9211 eq396754
  have eq399726 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq116842 X0 (k X0 X0)
       have i₂ := eq396767 X0
       grind)
    | exact superpose eq396767 eq116842
    | (have j0 := eq116842 X0 (k X0 X0)
       grind)
    | exact resolve eq116842 eq396767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405463 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq399726 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399726
  have eq408151 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq405463 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq405463
    | exact resolve eq405463 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408158 : (k y y) ≠ (k y (k y y)) ∨ (k y y) = (M.op (k y y) (k y (k y y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq405463 (k y y)
       have i₂ := eq149643 (k y y)
       grind)
    | exact superpose eq149643 eq405463
    | exact resolve eq405463 eq149643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405463
  have eq408167 : (k y y) = (M.op (k y y) (k y (k y y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq408158
       have r₂ := eq150535 y
       grind)
    | exact resolve eq408158 eq150535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150535 eq408158
  have eq408169 : (k y y) = (M.op (k y y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq408167
       have i₂ := eq396767 y
       grind)
    | exact superpose eq396767 eq408167
    | exact resolve eq408167 eq396767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408167
  have eq410984 : (M.op y y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq166101
       have i₂ := eq408169
       grind)
    | exact superpose eq408169 eq166101
    | exact resolve eq166101 eq408169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166101 eq408169
  have eq411000 : (M.op y y) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq410984
  have eq412276 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq146225
       have i₂ := eq411000
       grind)
    | exact superpose eq411000 eq146225
    | exact resolve eq146225 eq411000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146225
  have eq412287 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq149643 X0
       have i₂ := eq411000
       grind)
    | exact superpose eq411000 eq149643
    | exact resolve eq149643 eq411000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149643
  have eq412290 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op y y)) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq150160 X0
       have i₂ := eq411000
       grind)
    | exact superpose eq411000 eq150160
    | exact resolve eq150160 eq411000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150160
  have eq412331 : (M.op (σ y) (σ y)) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq382114
       have i₂ := eq411000
       grind)
    | exact superpose eq411000 eq382114
    | exact resolve eq382114 eq411000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382114 eq411000
  have eq412520 : (M.op (σ y) (σ y)) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq412331
  have eq412561 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op y y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq412290 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412290
  have eq412564 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq412287 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412287
  have eq412575 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq412276
  have eq444683 : (σ (M.op y y)) = (k (σ y) (σ (M.op (τ (σ (M.op y y))) (τ (σ (M.op y y)))))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26 (σ (M.op y y))
       have i₂ := eq412561 (σ (M.op (τ (σ (M.op y y))) (τ (σ (M.op y y)))))
       grind)
    | exact superpose eq412561 eq26
    | exact resolve eq26 eq412561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq412561
  have eq444785 : (σ (M.op y y)) = (σ (k y (M.op (τ (σ (M.op y y))) (τ (σ (M.op y y)))))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq444683
       have i₂ := eq15 y (M.op (τ (σ (M.op y y))) (τ (σ (M.op y y))))
       grind)
    | exact superpose eq15 eq444683
    | exact resolve eq444683 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444683
  have eq444847 : (σ (M.op y y)) = (σ (k y (M.op (M.op y y) (M.op y y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq444785
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq444785
    | exact resolve eq444785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444785
  have eq444874 : (σ (k y y)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq444847
       have i₂ := eq65 y
       grind)
    | exact superpose eq65 eq444847
    | exact resolve eq444847 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444847
  have eq446065 : ∀ X0 : G, (k (τ X0) (k y y)) = (τ (k X0 (σ (M.op y y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25 X0 (k y y)
       have i₂ := eq444874
       grind)
    | exact superpose eq444874 eq25
    | exact resolve eq25 eq444874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444874
  have eq446123 : ∀ X0 : G, (k (τ X0) (k y y)) = (k (τ X0) (M.op y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq446065 X0
       have i₂ := eq25 X0 (M.op y y)
       grind)
    | exact superpose eq25 eq446065
    | exact resolve eq446065 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq446065
  have eq732351 : ∀ X0 : G, (k X0 (k y y)) = (k X0 (M.op y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq446123 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq446123
    | exact resolve eq446123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446123
  have eq735897 : (k y (k y y)) = (k (M.op y y) (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq412564 (k y y)
       have i₂ := eq732351 (M.op y y)
       grind)
    | exact superpose eq732351 eq412564
    | exact resolve eq412564 eq732351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412564 eq732351
  have eq735955 : (k y (k y y)) = (k (M.op y y) (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq735897
  have eq735994 : y = (k (M.op y y) (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq735955
       have i₂ := eq396767 y
       grind)
    | exact superpose eq396767 eq735955
    | exact resolve eq735955 eq396767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396767 eq735955
  have eq742680 : (σ y) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq408151 (M.op y y)
       have i₂ := eq735994
       grind)
    | exact superpose eq735994 eq408151
    | exact resolve eq408151 eq735994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408151 eq735994
  have eq742709 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq742680
       have r₂ := eq412575
       grind)
    | exact resolve eq742680 eq412575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412575 eq742680
  have eq770221 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq412520
       have i₂ := eq742709
       grind)
    | exact superpose eq742709 eq412520
    | exact resolve eq412520 eq742709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412520 eq742709
  have eq770229 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq770221
  have eq774296 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq135737
       have i₂ := eq770229
       grind)
    | exact superpose eq770229 eq135737
    | exact resolve eq135737 eq770229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135737 eq770229
  have eq774330 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq774296
  have eq778323 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq774330
       grind)
    | exact superpose eq774330 eq16
    | exact resolve eq16 eq774330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774330
  have eq1329698 : x = (k x (τ (σ y))) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq263 x
       have i₂ := eq135738
       grind)
    | exact superpose eq135738 eq263
    | exact resolve eq263 eq135738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq135738
  have eq1329707 : (σ y) = (σ (k x y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1329698
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1329698
    | exact resolve eq1329698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329698
  have eq1329709 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1329707
       have i₂ := eq116842 x y
       grind)
    | exact superpose eq116842 eq1329707
    | (have j1 := eq116842 x y
       grind)
    | exact resolve eq1329707 eq116842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116842
  have eq1329711 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq121952 x y
       have i₂ := eq1329707
       grind)
    | exact superpose eq1329707 eq121952
    | (have j0 := eq121952 x y
       grind)
    | exact resolve eq121952 eq1329707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329707
  have eq1329722 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq1329711
  have eq1329724 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1329709
  have eq1329730 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1329722
       have r₂ := eq135708
       grind)
    | exact resolve eq1329722 eq135708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329722
  have eq1329732 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1329724
       have r₂ := eq135708
       grind)
    | exact resolve eq1329724 eq135708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135708 eq1329724
  have eq1329751 : y = (M.op x (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2247 x y
       have i₂ := eq1329730
       grind)
    | exact superpose eq1329730 eq2247
    | (have j0 := eq2247 x y
       grind)
    | exact resolve eq2247 eq1329730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq1329769 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq121952 x y
       have i₂ := eq1329730
       grind)
    | exact superpose eq1329730 eq121952
    | (have j0 := eq121952 x y
       grind)
    | exact resolve eq121952 eq1329730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121952 eq1329730
  have eq1329799 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1329769
  have eq1329817 : y = (M.op x (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq1329751
  have eq1335617 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1329732
       grind)
    | exact superpose eq1329732 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1329732
       grind)
    | exact resolve eq13 eq1329732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1335627 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq1335628 : y = (k x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1335617
  have eq1393765 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126159 x y
       have i₂ := eq1335628
       grind)
    | exact superpose eq1335628 eq126159
    | (have j0 := eq126159 x y
       grind)
    | exact resolve eq126159 eq1335628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126159 eq1335628
  have eq1393772 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1393765
  have eq1508661 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1393772
       grind)
    | exact superpose eq1393772 eq16
    | exact resolve eq16 eq1393772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393772
  have eq1520777 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1508661
       have i₂ := eq1329732
       grind)
    | exact superpose eq1329732 eq1508661
    | exact resolve eq1508661 eq1329732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329732 eq1508661
  have eq1520779 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1520777
  have eq1520780 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1520779
       have r₂ := eq1335627
       grind)
    | exact resolve eq1520779 eq1335627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520779
  have eq1520785 : y = (M.op x x) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1329817
       have i₂ := eq1520780
       grind)
    | exact superpose eq1520780 eq1329817
    | exact resolve eq1329817 eq1520780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329817 eq1520780
  have eq1520814 : y = (M.op x x) ∨ x = y := by grind
  clear eq1520785
  have eq1520833 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq61 x
       have i₂ := eq1520814
       grind)
    | exact superpose eq1520814 eq61
    | exact resolve eq61 eq1520814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1520814
  have eq1520946 : x = (M.op x y) := by
    first
    | (have r₁ := eq1520833
       have r₂ := eq1335627
       grind)
    | exact resolve eq1520833 eq1335627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335627 eq1520833
  have eq1537744 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq1520946
       grind)
    | exact superpose eq1520946 eq9
    | exact resolve eq9 eq1520946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1537771 : y = (M.op x x) := by
    first
    | (have i₁ := eq1537744
       have i₂ := eq1520946
       grind)
    | exact superpose eq1520946 eq1537744
    | exact resolve eq1537744 eq1520946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537744
  have eq1537778 : x = (k x y) := by grind
  have eq1537782 : x = (M.op y y) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq1537771
       grind)
    | exact superpose eq1537771 eq65
    | exact resolve eq65 eq1537771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1538057 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq778323
       have i₂ := eq1537782
       grind)
    | exact superpose eq1537782 eq778323
    | exact resolve eq778323 eq1537782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778323 eq1537782
  have eq1538169 : y = (M.op x y) := by
    first
    | (have r₁ := eq1538057
       have r₂ := eq1329799
       grind)
    | exact resolve eq1538057 eq1329799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329799 eq1538057
  have eq1538266 : x = y := by
    first
    | (have i₁ := eq1538169
       have i₂ := eq1520946
       grind)
    | exact superpose eq1520946 eq1538169
    | exact resolve eq1538169 eq1520946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520946 eq1538169
  have eq1538277 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1538266
       grind)
    | exact superpose eq1538266 eq16
    | exact resolve eq16 eq1538266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1538279 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq126082
       have i₂ := eq1538266
       grind)
    | exact superpose eq1538266 eq126082
    | exact resolve eq126082 eq1538266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126082
  have eq1538678 : x = (k x x) := by
    first
    | (have i₁ := eq1537778
       have i₂ := eq1538266
       grind)
    | exact superpose eq1538266 eq1537778
    | exact resolve eq1537778 eq1538266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537778
  have eq1538703 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1538279
       have i₂ := eq1537771
       grind)
    | exact superpose eq1537771 eq1538279
    | exact resolve eq1538279 eq1537771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538279
  have eq1538705 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1538277
       have i₂ := eq1537771
       grind)
    | exact superpose eq1537771 eq1538277
    | exact resolve eq1538277 eq1537771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537771 eq1538277
  have eq1538706 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1538703
       have i₂ := eq1538678
       grind)
    | exact superpose eq1538678 eq1538703
    | exact resolve eq1538703 eq1538678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538678 eq1538703
  have eq1538707 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1538705
       have i₂ := eq1538266
       grind)
    | exact superpose eq1538266 eq1538705
    | exact resolve eq1538705 eq1538266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538705
  have eq1538708 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1538706
       have i₂ := eq1538266
       grind)
    | exact superpose eq1538266 eq1538706
    | exact resolve eq1538706 eq1538266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538266 eq1538706
  have eq1538709 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1538708
  have eq1538710 : False := by grind
  exact eq1538710

/-- `Equation1256`: `x = x ◇ (((y ◇ y) ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_x_pxx_pxx_pyx_Equation1256 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1256 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1256.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op (M.op X1 X1) X2) X2)
       have i₂ := eq9 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq25 X0 x x X3
       have i₂ := eq9 (M.op X0 X0) x x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact superpose eq26 eq12
    | (have r₁ := eq12 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq26 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | (have i₁ := eq36 X0 X1
       have i₂ := eq26 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq26 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | (have r₁ := eq36 X0 (M.op X0 X0)
       have r₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact resolve eq36 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq39 (σ X0)
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq47
    | exact resolve eq47 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq47
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact superpose eq26 eq13
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | (have i₁ := eq55 X0 X1
       have i₂ := eq26 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq26 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 (k (M.op X0 X0) X1)
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq42 X0 X1
       grind)
    | (have r₁ := eq57 X0 (M.op X0 X0)
       have r₂ := eq42 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq42 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq57 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq57
  have eq71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq50 X1
       grind)
    | exact superpose eq50 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq50 X1
       grind)
    | exact superpose eq50 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq206 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq26
    | exact resolve eq26 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq87
    | (have j0 := eq87 (σ X0) X1
       grind)
    | exact resolve eq87 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq313 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq304 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq304 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq304 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq304 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq320 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq266
    | (have j0 := eq266 X0 X1
       grind)
    | exact resolve eq266 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq325 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq320 X0 X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq320
    | (have j0 := eq320 X0 X1
       grind)
    | exact resolve eq320 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq320
  have eq1070 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1076 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1070 X0 X1
       have j1 := eq325 X1 X0
       grind)
    | (have r₁ := eq1070 X1 X0
       have r₂ := eq325 X0 X1
       grind)
    | exact resolve eq1070 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq1070
  have eq1249 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq313 X1 (τ X0)
       grind)
    | exact superpose eq313 eq18
    | (have j1 := eq313 X1 X1
       grind)
    | exact resolve eq18 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1265 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 X0 X1
       have i₂ := eq313 X0 X2
       grind)
    | exact superpose eq313 eq206
    | (have j1 := eq313 X0 X2
       grind)
    | exact resolve eq206 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq313
  have eq2369 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1076 X1 X0
       grind)
    | exact superpose eq1076 eq10
    | (have j1 := eq1076 X1 X0
       grind)
    | exact resolve eq10 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq2403 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2369 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2369
    | (have j0 := eq2369 X0 X1
       grind)
    | exact resolve eq2369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369
  have eq5841 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1265 y (σ x) X0
       grind)
    | exact superpose eq1265 eq16
    | (have j1 := eq1265 y x X0
       grind)
    | exact resolve eq16 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq38268 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1249 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1249
    | (have j0 := eq1249 X0 X1
       grind)
    | exact resolve eq1249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq38699 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38268 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq38268
    | (have j0 := eq38268 X0 X1
       grind)
    | exact resolve eq38268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38268
  have eq39337 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2403 y x
       grind)
    | exact superpose eq2403 eq16
    | (have j1 := eq2403 y x
       grind)
    | exact resolve eq16 eq2403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq39576 : y = (M.op y y) := by
    first
    | (have j1 := eq38699 x y
       grind)
    | (have r₁ := eq39337
       have r₂ := eq38699 x y
       grind)
    | exact resolve eq39337 eq38699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38699 eq39337
  have eq39669 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 y X0
       have i₂ := eq39576
       grind)
    | exact superpose eq39576 eq26
    | exact resolve eq26 eq39576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq39672 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq59 y x
       have i₂ := eq39576
       grind)
    | exact superpose eq39576 eq59
    | exact resolve eq59 eq39576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq39576
  have eq40970 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq5841 X0
       have i₂ := eq39669 x
       grind)
    | exact superpose eq39669 eq5841
    | (have j0 := eq5841 X0
       grind)
    | exact resolve eq5841 eq39669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5841
  have eq40971 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq40970 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40970
  have eq40973 : ∀ X0 : G, (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40971 X0
       have i₂ := eq39669 X0
       grind)
    | exact superpose eq39669 eq40971
    | exact resolve eq40971 eq39669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39669 eq40971
  have eq42159 : ∀ X0 : G, y = X0 := by
    intro X0
    first
    | (have i₁ := eq39672 X0
       have i₂ := eq40973 X0
       grind)
    | exact superpose eq40973 eq39672
    | exact resolve eq39672 eq40973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39672 eq40973
  have eq42611 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42159 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq42159 eq16
    | exact resolve eq16 eq42159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43130 : False := by grind
  exact eq43130

/-- `Equation1256`: `x = x ◇ (((y ◇ y) ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_x_pxx_x_pyx_Equation1256 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1256 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1256.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op (M.op X1 X1) X2) X2)
       have i₂ := eq9 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq25 X0 x x X3
       have i₂ := eq9 (M.op X0 X0) x x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact superpose eq26 eq12
    | (have r₁ := eq12 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq26 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | (have i₁ := eq36 X0 X1
       have i₂ := eq26 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq26 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | (have r₁ := eq36 X0 (M.op X0 X0)
       have r₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact resolve eq36 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq39 (σ X0)
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq47
    | exact resolve eq47 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq47
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact superpose eq26 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | (have i₁ := eq55 X0 X1
       have i₂ := eq26 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq26 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 (k (M.op X0 X0) X1)
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq42 X0 X1
       grind)
    | (have r₁ := eq57 X0 (M.op X0 X0)
       have r₂ := eq42 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq42 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq57 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq57
  have eq71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq50 X1
       grind)
    | exact superpose eq50 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq50 X1
       grind)
    | exact superpose eq50 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq206 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq26
    | exact resolve eq26 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq87
    | (have j0 := eq87 (σ X0) X1
       grind)
    | exact resolve eq87 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq313 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq304 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq304 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq304 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq304 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq320 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq266
    | (have j0 := eq266 X0 X1
       grind)
    | exact resolve eq266 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq325 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq320 X0 X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq320
    | (have j0 := eq320 X0 X1
       grind)
    | exact resolve eq320 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq320
  have eq1070 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1076 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1070 X0 X1
       have j1 := eq325 X1 X0
       grind)
    | (have r₁ := eq1070 X1 X0
       have r₂ := eq325 X0 X1
       grind)
    | exact resolve eq1070 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq1070
  have eq1249 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq313 X1 (τ X0)
       grind)
    | exact superpose eq313 eq18
    | (have j1 := eq313 X1 X1
       grind)
    | exact resolve eq18 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1265 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 X0 X1
       have i₂ := eq313 X0 X2
       grind)
    | exact superpose eq313 eq206
    | (have j1 := eq313 X0 X2
       grind)
    | exact resolve eq206 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq313
  have eq2369 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1076 X1 X0
       grind)
    | exact superpose eq1076 eq10
    | (have j1 := eq1076 X1 X0
       grind)
    | exact resolve eq10 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq2403 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2369 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2369
    | (have j0 := eq2369 X0 X1
       grind)
    | exact resolve eq2369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369
  have eq5840 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1265 y (σ x) X0
       grind)
    | exact superpose eq1265 eq16
    | (have j1 := eq1265 y x X0
       grind)
    | exact resolve eq16 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq38268 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1249 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1249
    | (have j0 := eq1249 X0 X1
       grind)
    | exact resolve eq1249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq38699 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38268 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq38268
    | (have j0 := eq38268 X0 X1
       grind)
    | exact resolve eq38268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38268
  have eq39337 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2403 y x
       grind)
    | exact superpose eq2403 eq16
    | (have j1 := eq2403 y x
       grind)
    | exact resolve eq16 eq2403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq39576 : y = (M.op y y) := by
    first
    | (have j1 := eq38699 x y
       grind)
    | (have r₁ := eq39337
       have r₂ := eq38699 x y
       grind)
    | exact resolve eq39337 eq38699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38699 eq39337
  have eq39668 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 y X0
       have i₂ := eq39576
       grind)
    | exact superpose eq39576 eq26
    | exact resolve eq26 eq39576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq39671 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq59 y x
       have i₂ := eq39576
       grind)
    | exact superpose eq39576 eq59
    | exact resolve eq59 eq39576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq39576
  have eq40969 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq5840 X0
       have i₂ := eq39668 x
       grind)
    | exact superpose eq39668 eq5840
    | (have j0 := eq5840 X0
       grind)
    | exact resolve eq5840 eq39668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5840
  have eq40970 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq40969 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40969
  have eq40972 : ∀ X0 : G, (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40970 X0
       have i₂ := eq39668 X0
       grind)
    | exact superpose eq39668 eq40970
    | exact resolve eq40970 eq39668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39668 eq40970
  have eq42158 : ∀ X0 : G, y = X0 := by
    intro X0
    first
    | (have i₁ := eq39671 X0
       have i₂ := eq40972 X0
       grind)
    | exact superpose eq40972 eq39671
    | exact resolve eq39671 eq40972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39671 eq40972
  have eq42610 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42158 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq42158 eq16
    | exact resolve eq16 eq42158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43129 : False := by grind
  exact eq43129

/-- `Equation1256`: `x = x ◇ (((y ◇ y) ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pyx_x_pxx_pyx_Equation1256 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1256 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1256.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op (M.op X1 X1) X2) X2)
       have i₂ := eq9 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq21 X0 x x X3
       have i₂ := eq9 (M.op X0 X0) x x
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq73 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq75 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (τ X1)
       grind)
    | exact superpose eq32 eq18
    | exact resolve eq18 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (M.op X0 X0) X1
       have i₂ := eq32 X0 (σ X1)
       grind)
    | exact superpose eq32 eq73
    | exact resolve eq73 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | (have j1 := eq37 (σ X0)
       grind)
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (σ (M.op X0 X0))
       have i₂ := eq75 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq75 eq37
    | (have j0 := eq37 (σ (M.op X0 X0))
       grind)
    | exact resolve eq37 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq75
  have eq220 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq303 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq318 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq303 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq303 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq303 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq303 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq338 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq318 X1 (τ X0)
       grind)
    | exact superpose eq318 eq18
    | (have j1 := eq318 X1 X1
       grind)
    | exact resolve eq18 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq318 X0 X2
       grind)
    | exact superpose eq318 eq24
    | (have j1 := eq318 X0 X2
       grind)
    | exact resolve eq24 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq318 X0 X1
       grind)
    | exact superpose eq318 eq88
    | (have j1 := eq318 X0 X2
       grind)
    | exact resolve eq88 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq318
  have eq1133 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ (M.op X0 X0)) X1
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq24
    | exact resolve eq24 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq1215 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1133 X0 X1
       have i₂ := eq351 X0 X0 X2
       grind)
    | exact superpose eq351 eq1133
    | (have j1 := eq351 (σ X0) X1 X2
       grind)
    | exact resolve eq1133 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq1133
  have eq1895 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq99 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq2377 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1215 y (σ x) X0
       grind)
    | exact superpose eq1215 eq16
    | (have j1 := eq1215 y x X0
       grind)
    | exact resolve eq16 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq13953 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X1)) = (k (τ (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq354 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq354 eq15
    | (have j1 := eq354 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq13994 : ∀ X0 X1 X2 : G, (k X1 X2) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13953 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13953
    | (have j0 := eq13953 X0 X1 X2
       grind)
    | exact resolve eq13953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13953
  have eq18408 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq338 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq338
    | (have j0 := eq338 X0 X1
       grind)
    | exact resolve eq338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq18686 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18408 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18408
    | (have j0 := eq18408 X0 X1
       grind)
    | exact resolve eq18408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18408
  have eq18793 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X1 X1
       have i₂ := eq18686 X0 X1
       grind)
    | exact superpose eq18686 eq32
    | (have j1 := eq18686 X2 X0
       grind)
    | exact resolve eq32 eq18686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq18686
  have eq18937 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1895 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1895
    | (have j0 := eq1895 (τ X0)
       grind)
    | exact resolve eq1895 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1895
  have eq18959 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18937 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18937
    | (have j0 := eq18937 X0
       grind)
    | exact resolve eq18937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18937
  have eq18967 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18959 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18959
    | (have j0 := eq18959 X0
       grind)
    | exact resolve eq18959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18959
  have eq99846 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq13994 x y X0
       grind)
    | exact superpose eq13994 eq16
    | (have j1 := eq13994 X0 y X0
       grind)
    | exact resolve eq16 eq13994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13994
  have eq100147 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq99846 X0
       have j1 := eq18793 y X0 x
       grind)
    | (have r₁ := eq99846 X0
       have r₂ := eq18793 y x x
       grind)
    | exact resolve eq99846 eq18793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18793 eq99846
  have eq101601 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18967 y
       have i₂ := eq100147 y
       grind)
    | exact superpose eq100147 eq18967
    | (have j0 := eq18967 y
       grind)
    | (have r₁ := eq18967 y
       have r₂ := eq100147 y
       grind)
    | exact resolve eq18967 eq100147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18967
  have eq101742 : y = (M.op y y) := by grind
  clear eq101601
  have eq103178 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq101742
       grind)
    | exact superpose eq101742 eq24
    | exact resolve eq24 eq101742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq101742
  have eq104798 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2377 X0
       have i₂ := eq103178 x
       grind)
    | exact superpose eq103178 eq2377
    | (have j0 := eq2377 X0
       grind)
    | exact resolve eq2377 eq103178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq104799 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq104798 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104798
  have eq104803 : ∀ X0 : G, (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq104799 X0
       have i₂ := eq103178 X0
       grind)
    | exact superpose eq103178 eq104799
    | exact resolve eq104799 eq103178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103178 eq104799
  have eq106326 : ∀ X0 : G, y = X0 := by
    intro X0
    first
    | (have i₁ := eq100147 X0
       have i₂ := eq104803 X0
       grind)
    | exact superpose eq104803 eq100147
    | exact resolve eq100147 eq104803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100147 eq104803
  have eq108493 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106326 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq106326 eq16
    | exact resolve eq16 eq106326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109669 : False := by grind
  exact eq109669

/-- `Equation1264`: `x = x ◇ (((y ◇ z) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_x_pxx_x_pyx_Equation1264 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1264 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1264.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq9 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq25 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact superpose eq26 eq12
    | (have r₁ := eq12 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq26 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | (have i₁ := eq36 X0 X1
       have i₂ := eq26 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq26 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | (have r₁ := eq36 X0 (M.op X0 X0)
       have r₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact resolve eq36 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq39 (σ X0)
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq47
    | exact resolve eq47 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq47
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact superpose eq26 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | (have i₁ := eq55 X0 X1
       have i₂ := eq26 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq26 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 (k (M.op X0 X0) X1)
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq42 X0 X1
       grind)
    | (have r₁ := eq57 X0 (M.op X0 X0)
       have r₂ := eq42 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq42 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq57 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq57
  have eq71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq50 X1
       grind)
    | exact superpose eq50 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq50 X1
       grind)
    | exact superpose eq50 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq208 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq26
    | exact resolve eq26 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq86
    | (have j0 := eq86 (σ X0) X1
       grind)
    | exact resolve eq86 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq309 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq300 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq300 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq300 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq300 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq316 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq265
    | (have j0 := eq265 X0 X1
       grind)
    | exact resolve eq265 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq321 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq316
    | (have j0 := eq316 X0 X1
       grind)
    | exact resolve eq316 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq316
  have eq1015 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1019 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1015 X0 X1
       have j1 := eq321 X1 X0
       grind)
    | (have r₁ := eq1015 X1 X0
       have r₂ := eq321 X0 X1
       grind)
    | exact resolve eq1015 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq1015
  have eq1410 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq309 X1 (τ X0)
       grind)
    | exact superpose eq309 eq18
    | (have j1 := eq309 X1 X1
       grind)
    | exact resolve eq18 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1422 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq309 X0 X2
       grind)
    | exact superpose eq309 eq208
    | (have j1 := eq309 X0 X2
       grind)
    | exact resolve eq208 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq309
  have eq3022 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1019 X1 X0
       grind)
    | exact superpose eq1019 eq10
    | (have j1 := eq1019 X1 X0
       grind)
    | exact resolve eq10 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq3056 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3022 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3022
    | (have j0 := eq3022 X0 X1
       grind)
    | exact resolve eq3022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022
  have eq6920 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1422 y (σ x) X0
       grind)
    | exact superpose eq1422 eq16
    | (have j1 := eq1422 y x X0
       grind)
    | exact resolve eq16 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq39936 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1410 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1410
    | (have j0 := eq1410 X0 X1
       grind)
    | exact resolve eq1410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq40372 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39936 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq39936
    | (have j0 := eq39936 X0 X1
       grind)
    | exact resolve eq39936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39936
  have eq40996 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3056 y x
       grind)
    | exact superpose eq3056 eq16
    | (have j1 := eq3056 y x
       grind)
    | exact resolve eq16 eq3056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3056
  have eq41223 : y = (M.op y y) := by
    first
    | (have j1 := eq40372 x y
       grind)
    | (have r₁ := eq40996
       have r₂ := eq40372 x y
       grind)
    | exact resolve eq40996 eq40372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40372 eq40996
  have eq41310 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 y X0
       have i₂ := eq41223
       grind)
    | exact superpose eq41223 eq26
    | exact resolve eq26 eq41223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq41313 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq59 y x
       have i₂ := eq41223
       grind)
    | exact superpose eq41223 eq59
    | exact resolve eq59 eq41223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq41223
  have eq42232 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq6920 X0
       have i₂ := eq41310 x
       grind)
    | exact superpose eq41310 eq6920
    | (have j0 := eq6920 X0
       grind)
    | exact resolve eq6920 eq41310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6920
  have eq42233 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq42232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42232
  have eq42235 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq42233 X0
       have i₂ := eq41313 X0
       grind)
    | exact superpose eq41313 eq42233
    | exact resolve eq42233 eq41313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41313 eq42233
  have eq43340 : ∀ X0 : G, y = X0 := by
    intro X0
    first
    | (have i₁ := eq41310 X0
       have i₂ := eq42235 X0
       grind)
    | exact superpose eq42235 eq41310
    | exact resolve eq41310 eq42235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41310 eq42235
  have eq43952 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43340 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq43340 eq16
    | exact resolve eq16 eq43340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44469 : False := by grind
  exact eq44469

/-- `Equation1264`: `x = x ◇ (((y ◇ z) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pyx_x_pxx_pyx_Equation1264 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1264 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1264.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq9 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq21 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq72 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq74 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (τ X1)
       grind)
    | exact superpose eq32 eq18
    | exact resolve eq18 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (M.op X0 X0) X1
       have i₂ := eq32 X0 (σ X1)
       grind)
    | exact superpose eq32 eq72
    | exact resolve eq72 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | (have j1 := eq37 (σ X0)
       grind)
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (σ (M.op X0 X0))
       have i₂ := eq74 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq74 eq37
    | (have j0 := eq37 (σ (M.op X0 X0))
       grind)
    | exact resolve eq37 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq74
  have eq276 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq331 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq343 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq331 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq331 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq331 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq331 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq466 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq343 X1 (τ X0)
       grind)
    | exact superpose eq343 eq18
    | (have j1 := eq343 X1 X1
       grind)
    | exact resolve eq18 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq343 X0 X2
       grind)
    | exact superpose eq343 eq24
    | (have j1 := eq343 X0 X2
       grind)
    | exact resolve eq24 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq343 X0 X1
       grind)
    | exact superpose eq343 eq87
    | (have j1 := eq343 X0 X2
       grind)
    | exact resolve eq87 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq343
  have eq1244 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ (M.op X0 X0)) X1
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq24
    | exact resolve eq24 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq1332 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1244 X0 X1
       have i₂ := eq476 X0 X0 X2
       grind)
    | exact superpose eq476 eq1244
    | (have j1 := eq476 (σ X0) X1 X2
       grind)
    | exact resolve eq1244 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq1244
  have eq2450 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq98 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq3031 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1332 y (σ x) X0
       grind)
    | exact superpose eq1332 eq16
    | (have j1 := eq1332 y x X0
       grind)
    | exact resolve eq16 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq17749 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X1)) = (k (τ (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq480 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq480 eq15
    | (have j1 := eq480 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq17789 : ∀ X0 X1 X2 : G, (k X1 X2) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17749 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17749
    | (have j0 := eq17749 X0 X1 X2
       grind)
    | exact resolve eq17749 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17749
  have eq25658 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq466 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq466
    | (have j0 := eq466 X0 X1
       grind)
    | exact resolve eq466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq25973 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25658 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq25658
    | (have j0 := eq25658 X0 X1
       grind)
    | exact resolve eq25658 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25658
  have eq26098 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X1 X1
       have i₂ := eq25973 X0 X1
       grind)
    | exact superpose eq25973 eq32
    | (have j1 := eq25973 X2 X0
       grind)
    | exact resolve eq32 eq25973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq25973
  have eq26254 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2450 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2450
    | (have j0 := eq2450 (τ X0)
       grind)
    | exact resolve eq2450 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2450
  have eq26280 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26254 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26254
    | (have j0 := eq26254 X0
       grind)
    | exact resolve eq26254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26254
  have eq26289 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26280 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26280
    | (have j0 := eq26280 X0
       grind)
    | exact resolve eq26280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26280
  have eq110351 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq17789 x y X0
       grind)
    | exact superpose eq17789 eq16
    | (have j1 := eq17789 X0 y X0
       grind)
    | exact resolve eq16 eq17789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17789
  have eq110628 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq110351 X0
       have j1 := eq26098 y X0 x
       grind)
    | (have r₁ := eq110351 X0
       have r₂ := eq26098 y x x
       grind)
    | exact resolve eq110351 eq26098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26098 eq110351
  have eq112088 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq26289 y
       have i₂ := eq110628 y
       grind)
    | exact superpose eq110628 eq26289
    | (have j0 := eq26289 y
       grind)
    | (have r₁ := eq26289 y
       have r₂ := eq110628 y
       grind)
    | exact resolve eq26289 eq110628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26289
  have eq112214 : y = (M.op y y) := by grind
  clear eq112088
  have eq113473 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq112214
       grind)
    | exact superpose eq112214 eq24
    | exact resolve eq24 eq112214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq112214
  have eq115068 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq3031 X0
       have i₂ := eq113473 x
       grind)
    | exact superpose eq113473 eq3031
    | (have j0 := eq3031 X0
       grind)
    | exact resolve eq3031 eq113473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3031
  have eq115069 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq115068 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115068
  have eq115073 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq115069 X0
       have i₂ := eq110628 X0
       grind)
    | exact superpose eq110628 eq115069
    | exact resolve eq115069 eq110628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110628 eq115069
  have eq116560 : ∀ X0 : G, y = X0 := by
    intro X0
    first
    | (have i₁ := eq113473 X0
       have i₂ := eq115073 X0
       grind)
    | exact superpose eq115073 eq113473
    | exact resolve eq113473 eq115073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113473 eq115073
  have eq118842 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq116560 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq116560 eq16
    | exact resolve eq16 eq116560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119937 : False := by grind
  exact eq119937
