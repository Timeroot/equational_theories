import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq353 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq353 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq353 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq365 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq354 (σ X0)
       grind)
    | exact superpose eq354 eq15
    | exact resolve eq15 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq354 (τ X0)
       grind)
    | exact superpose eq354 eq31
    | exact resolve eq31 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq378 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq371
    | exact resolve eq371 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq384 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365 X0
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq365
    | exact resolve eq365 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq365
  have eq677 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq702 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 X1
       have i₂ := eq384 X1
       grind)
    | exact superpose eq384 eq677
    | (have j0 := eq677 X0 X1
       grind)
    | exact resolve eq677 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq716 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq702
    | (have j0 := eq702 X0 X1
       grind)
    | exact resolve eq702 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq3002 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq716
    | (have j0 := eq716 (τ X0) X1
       grind)
    | exact resolve eq716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq3071 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3002 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3002
    | (have j0 := eq3002 X0 X1
       grind)
    | exact resolve eq3002 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3002
  have eq3095 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3071 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq3071 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq3071 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3071
  have eq3099 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3095 X0 X1
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq3095
    | (have j0 := eq3095 X0 X1
       grind)
    | exact resolve eq3095 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095
  have eq3101 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3099 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3099
    | (have j0 := eq3099 X0 X1
       grind)
    | exact resolve eq3099 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099
  have eq3103 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3101 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3101
    | (have j0 := eq3101 X1 (τ X0)
       grind)
    | exact resolve eq3101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3123 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3101 (σ X1) X0
       grind)
    | exact superpose eq3101 eq15
    | (have j1 := eq3101 (σ X1) X0
       grind)
    | exact resolve eq15 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq3173 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3123 X0 X1
       have i₂ := eq384 X1
       grind)
    | exact superpose eq384 eq3123
    | (have j0 := eq3123 X0 X1
       grind)
    | exact resolve eq3123 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123
  have eq3191 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (M.op X0 X0))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3103 X0 X1
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq3103
    | (have j0 := eq3103 X0 X1
       grind)
    | exact resolve eq3103 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3103
  have eq3199 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3191 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3191
    | (have j0 := eq3191 X0 X1
       grind)
    | exact resolve eq3191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191
  have eq3235 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq3199 (τ X0) X1
       grind)
    | exact superpose eq3199 eq17
    | (have j1 := eq3199 X1 (τ X0)
       grind)
    | exact resolve eq17 eq3199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3199
  have eq3290 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3235 X0 X1
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq3235
    | (have j0 := eq3235 X0 X1
       grind)
    | exact resolve eq3235 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq3235
  have eq3648 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3290 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3290
    | (have j0 := eq3290 (σ X0) X1
       grind)
    | exact resolve eq3290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290
  have eq3720 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3648 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3648
    | (have j0 := eq3648 X0 X1
       grind)
    | exact resolve eq3648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3648
  have eq3727 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3720 X0 X1
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq3720
    | (have j0 := eq3720 X0 X1
       grind)
    | exact resolve eq3720 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq3730 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3727 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3727
    | (have j0 := eq3727 X0 X1
       grind)
    | exact resolve eq3727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3727
  have eq4277 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3173 x y
       grind)
    | exact superpose eq3173 eq16
    | (have j1 := eq3173 x y
       grind)
    | exact resolve eq16 eq3173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq4364 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq4277
       have i₂ := eq3730 x y
       grind)
    | exact superpose eq3730 eq4277
    | (have j1 := eq3730 x y
       grind)
    | (have r₁ := eq4277
       have r₂ := eq3730 x y
       grind)
    | exact resolve eq4277 eq3730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3730 eq4277
  have eq4365 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4364
  have eq4395 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y y
       have i₂ := eq4365
       grind)
    | exact superpose eq4365 eq61
    | exact resolve eq61 eq4365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4396 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq4365
       grind)
    | exact superpose eq4365 eq61
    | exact resolve eq61 eq4365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq4414 : (M.op x x) = (M.op y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67 x (M.op x y) x
       have i₂ := eq4395 x
       grind)
    | exact superpose eq4395 eq67
    | exact resolve eq67 eq4395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4395
  have eq4446 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4396 x
       have i₂ := eq4414
       grind)
    | exact superpose eq4414 eq4396
    | exact resolve eq4396 eq4414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396 eq4414
  have eq4465 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4446
  have eq4466 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4465
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq4465
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq4465
    | exact resolve eq4465 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4465
  have eq4467 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4466
       grind)
    | exact superpose eq4466 eq16
    | exact resolve eq16 eq4466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq4468 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4467
       have r₂ := eq384 x
       grind)
    | exact resolve eq4467 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467
  have eq4497 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq384 (M.op y y)
       have i₂ := eq4468
       grind)
    | exact superpose eq4468 eq384
    | exact resolve eq384 eq4468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468
  have eq4536 : (σ (M.op (M.op y y) (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq4497
       have i₂ := eq384 (M.op x x)
       grind)
    | exact superpose eq384 eq4497
    | exact resolve eq4497 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4497
  have eq4554 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq4536
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq4536
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq4536
    | exact resolve eq4536 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4536
  have eq4555 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4554
       have i₂ := eq61 y y y
       grind)
    | (have i₁ := eq4554
       have i₂ := eq61 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq61 eq4554
    | exact resolve eq4554 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq4554
  have eq4556 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4555
       grind)
    | exact superpose eq4555 eq16
    | exact resolve eq16 eq4555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4557 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4555
       grind)
    | exact superpose eq4555 eq10
    | exact resolve eq10 eq4555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4555
  have eq4630 : x = y := by
    first
    | (have i₁ := eq4557
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4557
    | exact resolve eq4557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq4631 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4556
       have i₂ := eq384 x
       grind)
    | exact superpose eq384 eq4556
    | exact resolve eq4556 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq4556
  have eq4632 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4631
       have i₂ := eq4630
       grind)
    | exact superpose eq4630 eq4631
    | exact resolve eq4631 eq4630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4630 eq4631
  have eq4633 : False := by grind
  exact eq4633

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq365 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq365 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq365 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq377 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq366 (σ X0)
       grind)
    | exact superpose eq366 eq15
    | exact resolve eq15 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq366 (τ X0)
       grind)
    | exact superpose eq366 eq31
    | exact resolve eq31 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq390 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq383 X0
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq383
    | exact resolve eq383 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq396 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq377 X0
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq377
    | exact resolve eq377 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq377
  have eq633 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq396 X1
       grind)
    | exact superpose eq396 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq672 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq2606 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq672
    | (have j0 := eq672 (τ X0) X1
       grind)
    | exact resolve eq672 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq2667 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2606 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2606
    | (have j0 := eq2606 X0 X1
       grind)
    | exact resolve eq2606 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606
  have eq2684 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2667 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq2667 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq2667 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq2686 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2684 X0 X1
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq2684
    | (have j0 := eq2684 X0 X1
       grind)
    | exact resolve eq2684 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684
  have eq2688 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2686 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2686
    | (have j0 := eq2686 X0 X1
       grind)
    | exact resolve eq2686 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686
  have eq2690 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2688 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2688
    | (have j0 := eq2688 X1 (τ X0)
       grind)
    | exact resolve eq2688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2710 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2688 (σ X1) X0
       grind)
    | exact superpose eq2688 eq15
    | (have j1 := eq2688 (σ X1) X0
       grind)
    | exact resolve eq15 eq2688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688
  have eq2747 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2710 X0 X1
       have i₂ := eq396 X1
       grind)
    | exact superpose eq396 eq2710
    | (have j0 := eq2710 X0 X1
       grind)
    | exact resolve eq2710 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710
  have eq2760 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2690 X0 X1
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq2690
    | (have j0 := eq2690 X0 X1
       grind)
    | exact resolve eq2690 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2690
  have eq2766 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2760 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2760
    | (have j0 := eq2760 X0 X1
       grind)
    | exact resolve eq2760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq2798 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq2766 X0 (τ X1)
       grind)
    | exact superpose eq2766 eq17
    | (have j1 := eq2766 X0 (τ X1)
       grind)
    | exact resolve eq17 eq2766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2766
  have eq2839 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2798 X0 X1
       have i₂ := eq390 X1
       grind)
    | exact superpose eq390 eq2798
    | (have j0 := eq2798 X0 X1
       grind)
    | exact resolve eq2798 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq2798
  have eq3140 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2839 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2839
    | (have j0 := eq2839 X1 (σ X0)
       grind)
    | exact resolve eq2839 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839
  have eq3218 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3140 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3140
    | (have j0 := eq3140 X0 X1
       grind)
    | exact resolve eq3140 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3140
  have eq3225 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3218 X0 X1
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq3218
    | (have j0 := eq3218 X0 X1
       grind)
    | exact resolve eq3218 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3218
  have eq3228 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3225 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3225
    | (have j0 := eq3225 X0 X1
       grind)
    | exact resolve eq3225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3225
  have eq3702 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2747 x y
       grind)
    | exact superpose eq2747 eq16
    | (have j1 := eq2747 x y
       grind)
    | exact resolve eq16 eq2747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747
  have eq3777 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3702
       have i₂ := eq3228 y x
       grind)
    | exact superpose eq3228 eq3702
    | (have j1 := eq3228 x y
       grind)
    | (have r₁ := eq3702
       have r₂ := eq3228 y x
       grind)
    | exact resolve eq3702 eq3228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228 eq3702
  have eq3778 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3777
  have eq3810 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y y
       have i₂ := eq3778
       grind)
    | exact superpose eq3778 eq61
    | exact resolve eq61 eq3778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3811 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq3778
       grind)
    | exact superpose eq3778 eq61
    | exact resolve eq61 eq3778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778
  have eq3831 : (M.op x x) = (M.op y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67 x (M.op x y) x
       have i₂ := eq3810 x
       grind)
    | exact superpose eq3810 eq67
    | exact resolve eq67 eq3810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq3810
  have eq3865 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3811 x
       have i₂ := eq3831
       grind)
    | exact superpose eq3831 eq3811
    | exact resolve eq3811 eq3831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811 eq3831
  have eq3886 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3865
  have eq3887 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3886
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq3886
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq3886
    | exact resolve eq3886 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3886
  have eq3888 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3887
       grind)
    | exact superpose eq3887 eq16
    | exact resolve eq16 eq3887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq3889 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq3888
       have r₂ := eq396 x
       grind)
    | exact resolve eq3888 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3888
  have eq3919 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq396 (M.op y y)
       have i₂ := eq3889
       grind)
    | exact superpose eq3889 eq396
    | exact resolve eq396 eq3889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq3960 : (σ (M.op (M.op y y) (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq3919
       have i₂ := eq396 (M.op x x)
       grind)
    | exact superpose eq396 eq3919
    | exact resolve eq3919 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq3978 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq3960
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq3960
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq3960
    | exact resolve eq3960 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3960
  have eq3979 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3978
       have i₂ := eq61 y y y
       grind)
    | (have i₁ := eq3978
       have i₂ := eq61 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq61 eq3978
    | exact resolve eq3978 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq3978
  have eq3980 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3979
       grind)
    | exact superpose eq3979 eq16
    | exact resolve eq16 eq3979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3981 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3979
       grind)
    | exact superpose eq3979 eq10
    | exact resolve eq10 eq3979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3979
  have eq4056 : x = y := by
    first
    | (have i₁ := eq3981
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3981
    | exact resolve eq3981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3981
  have eq4057 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3980
       have i₂ := eq396 x
       grind)
    | exact superpose eq396 eq3980
    | exact resolve eq3980 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq3980
  have eq4058 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4057
       have i₂ := eq4056
       grind)
    | exact superpose eq4056 eq4057
    | exact resolve eq4057 eq4056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4056 eq4057
  have eq4059 : False := by grind
  exact eq4059

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
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
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ X0 ∨ (k (M.op X0 X3) (M.op (M.op X1 X2) X0)) = (M.op (M.op X0 X3) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X3) (M.op (M.op X1 X2) X0)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X3) (M.op (M.op X1 X2) X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq113 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq113 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq113 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq113 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq119 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq114 sF2
       grind)
    | exact superpose eq114 eq49
    | exact resolve eq49 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq120 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq119
    | exact resolve eq119 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq130 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq104
       have i₂ := eq114 sF3
       grind)
    | exact superpose eq114 eq104
    | exact resolve eq104 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq131 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq130
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq130
    | exact resolve eq130 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq144 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq114 sF1
       grind)
    | exact superpose eq114 eq141
    | exact resolve eq141 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq147 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq114 sF0
       grind)
    | exact superpose eq114 eq144
    | exact resolve eq144 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq144
  have eq293 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) X0)) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq12
    | (have j0 := eq12 (M.op X0 X1) (M.op (M.op (σ x) (σ y)) X0)
       grind)
    | exact resolve eq12 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq52 X2 X0 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq320 eq50
    | exact resolve eq50 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq648 : ∀ X0 X1 X3 X4 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op (M.op X3 X4) (M.op X1 X0))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq68 (M.op X0 X4) X1 x (M.op X4 x)
       have i₂ := eq52 X0 X4 x
       grind)
    | exact superpose eq52 eq68
    | exact resolve eq68 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq68
  have eq8992 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq322 eq293
    | exact resolve eq293 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq9010 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51 eq8992
    | exact resolve eq8992 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq8992
  have eq11040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11040
    | exact resolve eq11040 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11040
  have eq11052 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11041
       have r₂ := eq27
       grind)
    | exact resolve eq11041 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11041
  have eq11056 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11052
    | exact resolve eq11052 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11052
  have eq11058 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11056
    | exact resolve eq11056 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11056
  have eq11297 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11058 eq322
    | exact resolve eq322 eq11058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11298 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11058 eq334
    | exact resolve eq334 eq11058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11058
  have eq11663 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11298 eq11297
    | exact resolve eq11297 eq11298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11297 eq11298
  have eq11708 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq11663
  have eq11717 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq320 x
       have i₂ := eq11708
       grind)
    | exact superpose eq11708 eq320
    | exact resolve eq320 eq11708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11718 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq332 y
       have i₂ := eq11708
       grind)
    | exact superpose eq11708 eq332
    | exact resolve eq332 eq11708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq11708
  have eq12024 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11717 eq147
    | exact resolve eq147 eq11717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11717
  have eq12093 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12024
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12024
    | exact resolve eq12024 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12024
  have eq12101 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11718 eq147
    | exact resolve eq147 eq11718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq11718
  have eq12168 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12101
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12101
    | exact resolve eq12101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12101
  have eq12707 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12168 eq12093
    | exact resolve eq12093 eq12168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12093 eq12168
  have eq12748 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq12707
  have eq12772 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12748 eq27
    | exact resolve eq27 eq12748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12785 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12748 eq322
    | exact resolve eq322 eq12748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq12786 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12748 eq334
    | exact resolve eq334 eq12748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12748
  have eq12927 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12785 eq12785
    | exact resolve eq12785 eq12785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12785
  have eq12960 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq12927
  have eq13005 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12960 eq131
    | exact resolve eq131 eq12960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13043 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (M.op (M.op X0 X1) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12960 eq648
    | (have r₁ := eq648 (σ y) (σ y) x x
       have r₂ := eq12960
       grind)
    | (have r₁ := eq648 y x x x
       have r₂ := eq12960
       grind)
    | exact resolve eq648 eq12960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq12960
  have eq13047 : ∀ X0 X1 : G, (σ y) = (k (σ y) (M.op (M.op X0 X1) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq13043 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13043
  have eq13068 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq13005
    | exact resolve eq13005 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13005
  have eq16421 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12786 eq13047
    | exact resolve eq13047 eq12786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12786 eq13047
  have eq16442 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq16421
  have eq16499 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16442 eq99
    | exact resolve eq99 eq16442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq16442
  have eq16524 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq16499
  have eq16538 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16524
       have r₂ := eq12772
       grind)
    | exact resolve eq16524 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12772 eq16524
  have eq17315 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq320 x
       have i₂ := eq16538
       grind)
    | exact superpose eq16538 eq320
    | exact resolve eq320 eq16538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16538
  have eq17719 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17315 eq357
    | exact resolve eq357 eq17315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq17315
  have eq35217 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13068
       have i₂ := eq17719
       grind)
    | exact superpose eq17719 eq13068
    | exact resolve eq13068 eq17719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13068 eq17719
  have eq35318 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq35217
  have eq35347 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35318 eq26
    | exact resolve eq26 eq35318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35362 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35318 eq131
    | exact resolve eq131 eq35318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq35318
  have eq35509 : (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120 eq35362
    | exact resolve eq35362 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35362
  have eq35542 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35347 eq120
    | exact resolve eq120 eq35347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq35347
  have eq36570 : y = (M.op (M.op x y) (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq320 y
       have i₂ := eq35509
       grind)
    | exact superpose eq35509 eq320
    | exact resolve eq320 eq35509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37065 : y = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36570
       have i₂ := eq35542
       grind)
    | exact superpose eq35542 eq36570
    | exact resolve eq36570 eq35542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36570
  have eq37137 : y = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by grind
  clear eq37065
  have eq37181 : ∀ X0 : G, y = (M.op (M.op X0 y) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37137 eq336
    | exact resolve eq336 eq37137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq37137
  have eq41238 : y = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37181 y
       have i₂ := eq35509
       grind)
    | exact superpose eq35509 eq37181
    | exact resolve eq37181 eq35509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35509 eq37181
  have eq41321 : y = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by grind
  clear eq41238
  have eq41437 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41321 eq53
    | exact resolve eq53 eq41321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq41321
  have eq41526 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41437
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41437
    | exact resolve eq41437 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq41437
  have eq41546 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35542
       have i₂ := eq41526
       grind)
    | exact superpose eq41526 eq35542
    | exact resolve eq35542 eq41526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35542 eq41526
  have eq41627 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq41546
  have eq41665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41627 eq15
    | exact resolve eq15 eq41627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41627
  have eq41737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq41665
    | exact resolve eq41665 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41665
  have eq41739 : y = (M.op x y) := by
    first
    | (have r₁ := eq41737
       have r₂ := eq27
       grind)
    | exact resolve eq41737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41737
  have eq41740 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41739 eq20
    | exact resolve eq20 eq41739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq41744 : y ≠ y ∨ (k y x) = (M.op y y) := by
    first
    | exact superpose eq41739 eq66
    | (have r₁ := eq66
       have r₂ := eq41739
       grind)
    | exact resolve eq66 eq41739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq41797 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq41739 eq320
    | exact resolve eq320 eq41739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq41739
  have eq41887 : (k y x) = (M.op y y) := by grind
  clear eq41744
  have eq41957 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41740
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41740
    | exact resolve eq41740 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41740
  have eq41982 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq41957 eq26
    | exact resolve eq26 eq41957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq42593 : y = (M.op y y) := by
    first
    | (have i₁ := eq41797 (M.op y x)
       have i₂ := eq41797 x
       grind)
    | exact superpose eq41797 eq41797
    | exact resolve eq41797 eq41797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41797
  have eq43406 : y = (k y x) := by
    first
    | (have i₁ := eq41887
       have i₂ := eq42593
       grind)
    | exact superpose eq42593 eq41887
    | exact resolve eq41887 eq42593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41887 eq42593
  have eq43413 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq43406
       grind)
    | exact superpose eq43406 eq75
    | exact resolve eq75 eq43406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq43406
  have eq43448 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq41957 eq43413
    | exact resolve eq43413 eq41957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43413
  have eq43459 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq43448
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43448
    | exact resolve eq43448 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq43448
  have eq43469 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq41957 eq43459
    | exact resolve eq43459 eq41957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43459
  have eq43494 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq43469 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq43469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43495 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq43494
  have eq43497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq41982 eq43495
    | exact resolve eq43495 eq41982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43495
  have eq43508 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq43497
       have r₂ := eq27
       grind)
    | exact resolve eq43497 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43497
  have eq43519 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq41982 eq43508
    | exact resolve eq43508 eq41982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41982 eq43508
  have eq43537 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq43519 eq334
    | exact resolve eq334 eq43519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq44145 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43537 eq9010
    | exact resolve eq9010 eq43537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9010
  have eq44146 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41957 eq44145
    | exact resolve eq44145 eq41957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44145
  have eq44147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43469 eq44146
    | exact resolve eq44146 eq43469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43469 eq44146
  have eq44148 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44147
       have r₂ := eq27
       grind)
    | exact resolve eq44147 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44147
  have eq44149 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43537 eq44148
    | exact resolve eq44148 eq43537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43537 eq44148
  have eq44150 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41957 eq44149
    | exact resolve eq44149 eq41957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44149
  have eq44151 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44150
       have r₂ := eq43519
       grind)
    | exact resolve eq44150 eq43519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43519 eq44150
  have eq44152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41957 eq44151
    | exact resolve eq44151 eq41957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41957 eq44151
  have eq44153 : False := by grind
  exact eq44153

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq17
  have eq23 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
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
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X1) (σ X0)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq22
    | exact resolve eq22 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq87 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq86
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq87
    | exact resolve eq87 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq87
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq109 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq23 X2 X0 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq195 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (σ X0) (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) (σ X0) X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X0) x
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq24
    | exact resolve eq24 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq168
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq168
    | (have j1 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq168 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq168
  have eq684 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq683
  have eq3804 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x y) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq24 y x x
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq24
    | exact resolve eq24 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3812 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq109 x x y
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq109
    | exact resolve eq109 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq32065 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3804 (M.op y x)
       have i₂ := eq23 x y x
       grind)
    | exact superpose eq23 eq3804
    | exact resolve eq3804 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3804
  have eq32413 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq196 y (σ x)
       have i₂ := eq32065
       grind)
    | exact superpose eq32065 eq196
    | exact resolve eq196 eq32065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32813 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq109 (σ y) (σ (M.op y y)) (σ x)
       have i₂ := eq32413
       grind)
    | exact superpose eq32413 eq109
    | exact resolve eq109 eq32413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq32413
  have eq32860 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32813
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq32813
    | exact resolve eq32813 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32813
  have eq33183 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (σ x) (σ y)
       have i₂ := eq32860
       grind)
    | exact superpose eq32860 eq23
    | exact resolve eq23 eq32860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32860
  have eq34349 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq33183 (σ y)
       have i₂ := eq32065
       grind)
    | exact superpose eq32065 eq33183
    | exact resolve eq33183 eq32065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32065 eq33183
  have eq34419 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq34349
  have eq34434 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34419
       have i₂ := eq195 y (σ x)
       grind)
    | exact superpose eq195 eq34419
    | exact resolve eq34419 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34419
  have eq34763 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq195 y X0
       have i₂ := eq34434
       grind)
    | exact superpose eq34434 eq195
    | exact resolve eq195 eq34434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37058 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34763 (σ y)
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq34763
    | exact resolve eq34763 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34763
  have eq40080 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37058
       have i₂ := eq34434
       grind)
    | exact superpose eq34434 eq37058
    | exact resolve eq37058 eq34434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34434 eq37058
  have eq40139 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq40080
  have eq40157 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq40139
       have i₂ := eq98 (M.op x y)
       grind)
    | exact superpose eq98 eq40139
    | exact resolve eq40139 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40139
  have eq40547 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq40157
       grind)
    | exact superpose eq40157 eq10
    | exact resolve eq10 eq40157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40157
  have eq40772 : x = y ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq40547
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40547
    | exact resolve eq40547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40547
  have eq41111 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40772
       grind)
    | exact superpose eq40772 eq16
    | exact resolve eq16 eq40772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40772
  have eq41112 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq41111
       have r₂ := eq98 x
       grind)
    | exact resolve eq41111 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41111
  have eq41517 : (M.op (M.op x y) (M.op x y)) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (M.op x y) (M.op x y))
       have i₂ := eq41112
       grind)
    | exact superpose eq41112 eq10
    | exact resolve eq10 eq41112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41534 : (τ (M.op (σ y) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq95 (M.op (M.op x y) (M.op x y))
       have i₂ := eq41112
       grind)
    | exact superpose eq41112 eq95
    | exact resolve eq95 eq41112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41753 : (M.op x y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq41534
       have i₂ := eq9 (M.op x y) x y (M.op x y)
       grind)
    | exact superpose eq9 eq41534
    | exact resolve eq41534 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41534
  have eq41766 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq41517
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq41517
    | exact resolve eq41517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41517
  have eq41768 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq41753
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq41753
    | exact resolve eq41753 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq41753
  have eq106458 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3812 (M.op x x)
       have i₂ := eq23 x x y
       grind)
    | exact superpose eq23 eq3812
    | exact resolve eq3812 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812
  have eq107318 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq195 x (σ y)
       have i₂ := eq106458
       grind)
    | exact superpose eq106458 eq195
    | exact resolve eq195 eq106458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq107433 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24 (σ x) (σ y) (σ (M.op x x))
       have i₂ := eq107318
       grind)
    | exact superpose eq107318 eq24
    | exact resolve eq24 eq107318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq107318
  have eq107553 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107433
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq107433
    | exact resolve eq107433 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107433
  have eq107628 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) (σ y) X0
       have i₂ := eq107553
       grind)
    | exact superpose eq107553 eq23
    | exact resolve eq23 eq107553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107553
  have eq108488 : ∀ X0 : G, y = (M.op (M.op x x) (M.op x x)) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq41766
       have i₂ := eq107628 X0
       grind)
    | exact superpose eq107628 eq41766
    | (have j1 := eq107628 X0
       grind)
    | exact resolve eq41766 eq107628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41766 eq107628
  have eq108590 : ∀ X0 : G, x = y ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq108488 X0
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq108488 X0
       have i₂ := eq23 X0 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq23 eq108488
    | (have j0 := eq108488 X0
       grind)
    | exact resolve eq108488 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108488
  have eq109308 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq108590 X0
       grind)
    | exact superpose eq108590 eq16
    | (have j1 := eq108590 X0
       grind)
    | exact resolve eq16 eq108590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108590
  have eq109350 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq109308 X0
       grind)
    | (have r₁ := eq109308 X0
       have r₂ := eq98 x
       grind)
    | exact resolve eq109308 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109308
  have eq109985 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq109350 (σ x)
       have i₂ := eq106458
       grind)
    | exact superpose eq106458 eq109350
    | exact resolve eq109350 eq106458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106458
  have eq110006 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq197 x (M.op (σ y) x)
       have i₂ := eq109350 x
       grind)
    | exact superpose eq109350 eq197
    | exact resolve eq197 eq109350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq109350
  have eq110131 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109985
       have i₂ := eq196 x (σ y)
       grind)
    | exact superpose eq196 eq109985
    | exact resolve eq109985 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq109985
  have eq110772 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110006
       grind)
    | exact superpose eq110006 eq16
    | exact resolve eq16 eq110006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110006
  have eq112492 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41112
       have i₂ := eq110131
       grind)
    | exact superpose eq110131 eq41112
    | exact resolve eq41112 eq110131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41112 eq110131
  have eq112630 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq112492
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq112492
       have i₂ := eq23 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq23 eq112492
    | exact resolve eq112492 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq112492
  have eq112631 : (σ x) = (σ y) := by grind
  clear eq112630
  have eq112679 : (σ (M.op y y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq98 y
       have i₂ := eq112631
       grind)
    | exact superpose eq112631 eq98
    | exact resolve eq98 eq112631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112631
  have eq113098 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq112679
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq112679
    | exact resolve eq112679 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq112679
  have eq113114 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq113098
       have i₂ := eq41768
       grind)
    | exact superpose eq41768 eq113098
    | exact resolve eq113098 eq41768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41768 eq113098
  have eq113115 : False := by grind
  exact eq113115

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq22 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq30 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq32 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq32 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq37
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq123 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq127 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq123 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | (have r₁ := eq123 X0 X1
       have r₂ := eq44 X0 X1
       grind)
    | (have r₁ := eq123 X0 X0
       have r₂ := eq44 X0 X0
       grind)
    | exact resolve eq123 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq123
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq127 (σ X0) (σ X1)
       grind)
    | exact superpose eq127 eq15
    | exact resolve eq15 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq127 X0 X1
       grind)
    | exact superpose eq127 eq235
    | exact resolve eq235 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq235
  have eq244 : False := by grind
  exact eq244

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq61 X3 X0 x
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
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
  have eq346 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq348 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq349 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq350 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq347 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq347 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq347 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq366 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq350 (σ X0)
       grind)
    | exact superpose eq350 eq15
    | exact resolve eq15 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq366 X0
       have i₂ := eq350 X0
       grind)
    | exact superpose eq350 eq366
    | exact resolve eq366 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq433 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq61
    | exact resolve eq61 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) X1 (σ X0)
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq67
    | exact resolve eq67 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq349 X0 (τ X1)
       grind)
    | exact superpose eq349 eq18
    | (have j1 := eq349 X0 (τ X1)
       grind)
    | exact resolve eq18 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq480 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq349 (σ X0) (σ X1)
       grind)
    | exact superpose eq349 eq15
    | (have j1 := eq349 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq1062 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq477 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq477
    | exact resolve eq477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq1124 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1062 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1062
    | (have j0 := eq1062 X0 X1
       grind)
    | exact resolve eq1062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1876 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq480 x y
       grind)
    | exact superpose eq480 eq16
    | (have j1 := eq480 x y
       grind)
    | exact resolve eq16 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1921 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq2065 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1876
       have i₂ := eq1124 y x
       grind)
    | exact superpose eq1124 eq1876
    | (have j1 := eq1124 (σ y) (σ x)
       grind)
    | (have r₁ := eq1876
       have r₂ := eq1124 y x
       grind)
    | exact resolve eq1876 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq2066 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2065
  have eq2075 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2066
       grind)
    | exact superpose eq2066 eq61
    | exact resolve eq61 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2076 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y x
       have i₂ := eq2066
       grind)
    | exact superpose eq2066 eq62
    | exact resolve eq62 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2136 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2076 y
       have i₂ := eq2066
       grind)
    | exact superpose eq2066 eq2076
    | exact resolve eq2076 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066 eq2076
  have eq2154 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq2136
  have eq2168 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq2154
       grind)
    | exact superpose eq2154 eq61
    | exact resolve eq61 eq2154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154
  have eq2273 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2168 (M.op x (σ x))
       have i₂ := eq2168 x
       grind)
    | exact superpose eq2168 eq2168
    | exact resolve eq2168 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168
  have eq2299 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2273
  have eq2302 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2299
       have i₂ := eq385 x
       grind)
    | exact superpose eq385 eq2299
    | exact resolve eq2299 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299
  have eq2334 : ∀ X0 X1 : G, (σ x) = (σ (M.op x x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq69 x X1 x x
       have i₂ := eq2302
       grind)
    | exact superpose eq2302 eq69
    | exact resolve eq69 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2302
  have eq2551 : ∀ X0 X1 : G, (τ (σ x)) = (M.op x x) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2334 X0 X1
       grind)
    | exact superpose eq2334 eq10
    | (have j1 := eq2334 X0 X1
       grind)
    | exact resolve eq10 eq2334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2610 : ∀ X0 X1 : G, x = (M.op x x) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2551 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2551
    | (have j0 := eq2551 X0 X1
       grind)
    | exact resolve eq2551 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551
  have eq2642 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op (M.op (M.op X1 X2) x) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 x X1 x
       have i₂ := eq2610 X0 X1
       grind)
    | exact superpose eq2610 eq67
    | (have j1 := eq2610 X1 X2
       grind)
    | exact resolve eq67 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2610
  have eq2704 : ∀ X0 X1 : G, x ≠ x ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq2642 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2642
  have eq2705 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq2704 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704
  have eq2758 : x = (M.op x x) := by
    first
    | (have i₁ := eq2705 (M.op x x) x
       have i₂ := eq2705 x x
       grind)
    | exact superpose eq2705 eq2705
    | exact resolve eq2705 eq2705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2773 : ∀ X2 : G, x = (M.op x (M.op x X2)) := by
    intro X2
    first
    | (have i₁ := eq61 (M.op (M.op x x) x) x X2
       have i₂ := eq2705 x x
       grind)
    | exact superpose eq2705 eq61
    | exact resolve eq61 eq2705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2705
  have eq2790 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq436 x x
       have i₂ := eq2758
       grind)
    | exact superpose eq2758 eq436
    | exact resolve eq436 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq2839 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op x X0) x) ∨ x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x (M.op x X0)
       have i₂ := eq2773 X0
       grind)
    | exact superpose eq2773 eq13
    | (have j0 := eq13 x (M.op x X0)
       grind)
    | (have r₁ := eq13 x (M.op x x)
       have r₂ := eq2773 x
       grind)
    | exact resolve eq13 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773
  have eq2852 : ∀ X0 : G, x = (k x (M.op x X0)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq2839 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839
  have eq2946 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (M.op X0 (σ x))
       have i₂ := eq2790 X0
       grind)
    | exact superpose eq2790 eq12
    | (have j0 := eq12 (σ x) (M.op X0 (σ x))
       grind)
    | (have r₁ := eq12 (σ x) (M.op X0 (σ x))
       have r₂ := eq2790 X0
       grind)
    | exact resolve eq12 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790
  have eq2959 : ∀ X0 : G, (k (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq2946 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946
  have eq3559 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x X0))) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1921 x (M.op x X0)
       have i₂ := eq2852 X0
       grind)
    | exact superpose eq2852 eq1921
    | (have j0 := eq1921 x (M.op x X0)
       have j1 := eq2852 X0
       grind)
    | exact resolve eq1921 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921 eq2852
  have eq3564 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x X0))) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq3559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3559
  have eq3660 : ∀ X0 : G, (k x (τ (M.op X0 (σ x)))) = (τ (M.op (σ x) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq28 x (M.op X0 (σ x))
       have i₂ := eq2959 X0
       grind)
    | exact superpose eq2959 eq28
    | exact resolve eq28 eq2959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2959
  have eq3811 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k x (τ (M.op (M.op (σ x) X0) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq3660 (M.op (σ x) X0)
       have i₂ := eq62 (σ x) X0 (σ x)
       grind)
    | exact superpose eq62 eq3660
    | exact resolve eq3660 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq3660
  have eq4613 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3564 (M.op y x)
       have i₂ := eq2075 x
       grind)
    | exact superpose eq2075 eq3564
    | exact resolve eq3564 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564
  have eq4658 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4613
  have eq4672 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2075 x
       have i₂ := eq4658
       grind)
    | exact superpose eq4658 eq2075
    | exact resolve eq2075 eq4658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075 eq4658
  have eq4700 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4672
  have eq4701 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4700
       have i₂ := eq2758
       grind)
    | exact superpose eq2758 eq4700
    | exact resolve eq4700 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4700
  have eq4702 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4701
       grind)
    | exact superpose eq4701 eq16
    | exact resolve eq16 eq4701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4701
  have eq4723 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4702
       have r₂ := eq385 x
       grind)
    | exact resolve eq4702 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq4702
  have eq4728 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4723
       grind)
    | exact superpose eq4723 eq16
    | exact resolve eq16 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4735 : (σ y) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq433 y (σ x)
       have i₂ := eq4723
       grind)
    | exact superpose eq4723 eq433
    | exact resolve eq433 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq4739 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4723
       grind)
    | exact superpose eq4723 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4723
       grind)
    | exact resolve eq13 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723
  have eq4756 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq4739
  have eq4757 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4756
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4756
    | exact resolve eq4756 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4756
  have eq4780 : (τ (σ y)) = (k x (τ (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq3811 (σ (M.op y y))
       have i₂ := eq4735
       grind)
    | exact superpose eq4735 eq3811
    | exact resolve eq3811 eq4735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811 eq4735
  have eq4814 : y = (k x (τ (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq4780
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4780
    | exact resolve eq4780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4780
  have eq5285 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1124 y x
       have i₂ := eq4757
       grind)
    | exact superpose eq4757 eq1124
    | (have j0 := eq1124 y x
       grind)
    | exact resolve eq1124 eq4757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124 eq4757
  have eq5338 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq5285
       have r₂ := eq4728
       grind)
    | exact resolve eq5285 eq4728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5285
  have eq5366 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4728
       have i₂ := eq5338
       grind)
    | exact superpose eq5338 eq4728
    | exact resolve eq4728 eq5338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5338
  have eq5405 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq5366
  have eq5408 : y = (k x (τ (σ x))) := by
    first
    | (have i₁ := eq4814
       have i₂ := eq5405
       grind)
    | exact superpose eq5405 eq4814
    | exact resolve eq4814 eq5405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4814 eq5405
  have eq5455 : y = (k x x) := by
    first
    | (have i₁ := eq5408
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5408
    | exact resolve eq5408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408
  have eq5463 : y = (M.op x x) := by
    first
    | (have i₁ := eq5455
       have i₂ := eq350 x
       grind)
    | exact superpose eq350 eq5455
    | exact resolve eq5455 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq5455
  have eq5465 : x = y := by
    first
    | (have i₁ := eq5463
       have i₂ := eq2758
       grind)
    | exact superpose eq2758 eq5463
    | exact resolve eq5463 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463
  have eq5489 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4728
       have i₂ := eq5465
       grind)
    | exact superpose eq5465 eq4728
    | exact resolve eq4728 eq5465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4728 eq5465
  have eq5507 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5489
       have i₂ := eq2758
       grind)
    | exact superpose eq2758 eq5489
    | exact resolve eq5489 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758 eq5489
  have eq5508 : False := by grind
  exact eq5508

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq61 X3 X0 x
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq350 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq351 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq352 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq347 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq347 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq347 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq368 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq352 (σ X0)
       grind)
    | exact superpose eq352 eq15
    | exact resolve eq15 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq352 (τ X0)
       grind)
    | exact superpose eq352 eq31
    | exact resolve eq31 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq374 X0
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq374
    | exact resolve eq374 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq387 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq368
    | exact resolve eq368 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq368
  have eq435 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq61
    | exact resolve eq61 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X1
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq61
    | exact resolve eq61 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq351 (σ X0) (σ X1)
       grind)
    | exact superpose eq351 eq15
    | (have j1 := eq351 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq351 (σ X0) X1
       grind)
    | exact superpose eq351 eq28
    | (have j1 := eq351 (σ X0) X1
       grind)
    | exact resolve eq28 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq490 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq351 (τ X0) X1
       grind)
    | exact superpose eq351 eq17
    | (have j1 := eq351 (τ X0) X1
       grind)
    | exact resolve eq17 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq351
  have eq1064 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq490 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq490
    | exact resolve eq490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1123 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1064 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1064
    | (have j0 := eq1064 X0 X1
       grind)
    | exact resolve eq1064 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1265 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (M.op (σ X0) X1))) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq487 (M.op X0 X0) (M.op (σ X0) X1)
       have i₂ := eq436 X0 X1
       grind)
    | exact superpose eq436 eq487
    | exact resolve eq487 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq487
  have eq1299 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1265 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1265
    | (have j0 := eq1265 X0 X1
       grind)
    | exact resolve eq1265 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq1902 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq482 x y
       grind)
    | exact superpose eq482 eq16
    | (have j1 := eq482 x y
       grind)
    | exact resolve eq16 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1947 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq482 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq1999 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1947 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1947
    | (have j0 := eq1947 (τ X0) (τ X1)
       grind)
    | exact resolve eq1947 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2007 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1999 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1999
    | (have j0 := eq1999 X0 X1
       grind)
    | exact resolve eq1999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2010 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2007 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2007
    | (have j0 := eq2007 X0 X1
       grind)
    | exact resolve eq2007 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2011 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2010 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2010
    | (have j0 := eq2010 X0 X1
       grind)
    | exact resolve eq2010 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2012 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2011 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2011
    | (have j0 := eq2011 X0 X1
       grind)
    | exact resolve eq2011 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1902
       have i₂ := eq1123 x y
       grind)
    | exact superpose eq1123 eq1902
    | (have j1 := eq1123 (σ x) (σ y)
       grind)
    | (have r₁ := eq1902
       have r₂ := eq1123 x y
       grind)
    | exact resolve eq1902 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2101 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2100
  have eq2107 : y ≠ y ∨ x = (M.op y x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2101
       grind)
    | exact superpose eq2101 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2101
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2101
       grind)
    | exact resolve eq13 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2109 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2101
       grind)
    | exact superpose eq2101 eq61
    | exact resolve eq61 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2118 : y = (k x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2107
  have eq2148 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2109 (M.op y x)
       have i₂ := eq2109 x
       grind)
    | exact superpose eq2109 eq2109
    | exact resolve eq2109 eq2109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq2166 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2148
  have eq2171 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq435 y (σ x)
       have i₂ := eq2166
       grind)
    | exact superpose eq2166 eq435
    | exact resolve eq435 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq2177 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq2166
       grind)
    | exact superpose eq2166 eq61
    | exact resolve eq61 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2166
  have eq2390 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2177 (σ (M.op y y))
       have i₂ := eq2171
       grind)
    | exact superpose eq2171 eq2177
    | exact resolve eq2177 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171 eq2177
  have eq2412 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2390
  have eq2416 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2412
       have i₂ := eq387 y
       grind)
    | exact superpose eq387 eq2412
    | exact resolve eq2412 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412
  have eq2449 : ∀ X0 X1 : G, (σ y) = (σ (M.op y y)) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq69 y X1 x y
       have i₂ := eq2416
       grind)
    | exact superpose eq2416 eq69
    | exact resolve eq69 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2416
  have eq2782 : ∀ X0 X1 : G, (τ (σ y)) = (M.op y y) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2449 X0 X1
       grind)
    | exact superpose eq2449 eq10
    | (have j1 := eq2449 X0 X1
       grind)
    | exact resolve eq10 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq2841 : ∀ X0 X1 : G, y = (M.op y y) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq2782 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2782
    | (have j0 := eq2782 X0 X1
       grind)
    | exact resolve eq2782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2782
  have eq2874 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 y) y) ∨ y = (M.op (M.op (M.op X1 X2) y) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 y X1 y
       have i₂ := eq2841 X0 X1
       grind)
    | exact superpose eq2841 eq67
    | (have j1 := eq2841 X1 X2
       grind)
    | exact resolve eq67 eq2841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2841
  have eq2939 : ∀ X0 X1 : G, y ≠ y ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have j0 := eq2874 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874
  have eq2940 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have j0 := eq2939 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939
  have eq2999 : y = (M.op y y) := by
    first
    | (have i₁ := eq2940 (M.op x x) y
       have i₂ := eq2940 x x
       grind)
    | exact superpose eq2940 eq2940
    | exact resolve eq2940 eq2940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2940
  have eq6298 : ∀ X0 X1 : G, (τ X0) = (k (M.op (τ X0) (τ X0)) (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1299 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1299
    | exact resolve eq1299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq6376 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X0)) (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6298 X0 X1
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq6298
    | (have j0 := eq6298 X0 X1
       grind)
    | exact resolve eq6298 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq6298
  have eq6387 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6376 X0 X1
       have i₂ := eq31 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact superpose eq31 eq6376
    | (have j0 := eq6376 X0 X1
       grind)
    | exact resolve eq6376 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq6376
  have eq6486 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op X0 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (M.op X0 X0) (M.op X0 X1))
       have i₂ := eq6387 X0 X1
       grind)
    | exact superpose eq6387 eq11
    | (have j1 := eq6387 X0 X1
       grind)
    | exact resolve eq11 eq6387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq6514 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6486 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6486
    | (have j0 := eq6486 X0 X1
       grind)
    | exact resolve eq6486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6486
  have eq6608 : ∀ X0 : G, y = (k y (M.op y X0)) ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq6514 y X0
       have i₂ := eq2999
       grind)
    | exact superpose eq2999 eq6514
    | (have j0 := eq6514 y X0
       grind)
    | exact resolve eq6514 eq2999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999 eq6514
  have eq8843 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1947 x y
       have i₂ := eq2118
       grind)
    | exact superpose eq2118 eq1947
    | (have j0 := eq1947 x y
       grind)
    | exact resolve eq1947 eq2118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947 eq2118
  have eq8856 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq8843
  have eq8857 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8856
  have eq8887 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq8857
       grind)
    | exact superpose eq8857 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8857
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8857
       grind)
    | exact resolve eq12 eq8857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8857
  have eq8909 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8887
  have eq10037 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1902
       have i₂ := eq8909
       grind)
    | exact superpose eq8909 eq1902
    | exact resolve eq1902 eq8909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902 eq8909
  have eq10045 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10037
  have eq10046 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10045
  have eq10050 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10046
       grind)
    | exact superpose eq10046 eq16
    | exact resolve eq16 eq10046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10064 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq10046
       grind)
    | exact superpose eq10046 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10046
       grind)
    | exact resolve eq12 eq10046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10065 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq10046
       grind)
    | exact superpose eq10046 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq10046
       grind)
    | exact resolve eq13 eq10046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10046
  have eq10086 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq10065
  have eq10087 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
  clear eq10064
  have eq10091 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10086
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq10086
    | exact resolve eq10086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10086
  have eq10092 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq10087
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq10087
    | exact resolve eq10087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10087
  have eq12177 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1123 x y
       have i₂ := eq10091
       grind)
    | exact superpose eq10091 eq1123
    | (have j0 := eq1123 x y
       grind)
    | exact resolve eq1123 eq10091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123 eq10091
  have eq12262 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq12177
       have r₂ := eq10050
       grind)
    | exact resolve eq12177 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12177
  have eq12287 : y = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12262
       have i₂ := eq10092
       grind)
    | exact superpose eq10092 eq12262
    | exact resolve eq12262 eq10092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10092 eq12262
  have eq12350 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10050
       have i₂ := eq12287
       grind)
    | exact superpose eq12287 eq10050
    | exact resolve eq10050 eq12287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10050 eq12287
  have eq12387 : (σ x) = (σ (k y x)) := by grind
  clear eq12350
  have eq12424 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq12387
       grind)
    | exact superpose eq12387 eq10
    | exact resolve eq10 eq12387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12387
  have eq12487 : x = (k y x) := by
    first
    | (have i₁ := eq12424
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12424
    | exact resolve eq12424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12424
  have eq12547 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2012 y x
       have i₂ := eq12487
       grind)
    | exact superpose eq12487 eq2012
    | (have j0 := eq2012 y x
       grind)
    | (have r₁ := eq2012 y x
       have r₂ := eq12487
       grind)
    | exact resolve eq2012 eq12487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012
  have eq12556 : x = (M.op y x) := by grind
  clear eq12547
  have eq12587 : y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq6608 x
       have i₂ := eq12556
       grind)
    | exact superpose eq12556 eq6608
    | exact resolve eq6608 eq12556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6608 eq12556
  have eq12623 : x = y ∨ x = y := by
    first
    | (have i₁ := eq12587
       have i₂ := eq12487
       grind)
    | exact superpose eq12487 eq12587
    | exact resolve eq12587 eq12487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12487 eq12587
  have eq12624 : x = y := by grind
  clear eq12623
  have eq12632 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12624
       grind)
    | exact superpose eq12624 eq16
    | exact resolve eq16 eq12624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12624
  have eq12783 : False := by grind
  exact eq12783

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pyx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq365 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq365 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq365 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq377 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq366 (σ X0)
       grind)
    | exact superpose eq366 eq15
    | exact resolve eq15 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq366 (τ X0)
       grind)
    | exact superpose eq366 eq31
    | exact resolve eq31 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq390 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq383 X0
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq383
    | exact resolve eq383 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq396 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq377 X0
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq377
    | exact resolve eq377 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq377
  have eq633 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq396 X1
       grind)
    | exact superpose eq396 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq672 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq2614 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq672
    | (have j0 := eq672 (τ X0) X1
       grind)
    | exact resolve eq672 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq2675 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2614 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2614
    | (have j0 := eq2614 X0 X1
       grind)
    | exact resolve eq2614 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614
  have eq2692 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2675 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq2675 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq2675 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2675
  have eq2694 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2692 X0 X1
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq2692
    | (have j0 := eq2692 X0 X1
       grind)
    | exact resolve eq2692 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692
  have eq2696 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2694 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2694
    | (have j0 := eq2694 X0 X1
       grind)
    | exact resolve eq2694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694
  have eq2698 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2696 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2696
    | (have j0 := eq2696 X1 (τ X0)
       grind)
    | exact resolve eq2696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2718 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2696 (σ X1) X0
       grind)
    | exact superpose eq2696 eq15
    | (have j1 := eq2696 (σ X1) X0
       grind)
    | exact resolve eq15 eq2696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2696
  have eq2755 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2718 X0 X1
       have i₂ := eq396 X1
       grind)
    | exact superpose eq396 eq2718
    | (have j0 := eq2718 X0 X1
       grind)
    | exact resolve eq2718 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718
  have eq2768 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2698 X0 X1
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq2698
    | (have j0 := eq2698 X0 X1
       grind)
    | exact resolve eq2698 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698
  have eq2774 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2768 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2768
    | (have j0 := eq2768 X0 X1
       grind)
    | exact resolve eq2768 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq2806 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq2774 X0 (τ X1)
       grind)
    | exact superpose eq2774 eq17
    | (have j1 := eq2774 X0 (τ X1)
       grind)
    | exact resolve eq17 eq2774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2774
  have eq2847 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2806 X0 X1
       have i₂ := eq390 X1
       grind)
    | exact superpose eq390 eq2806
    | (have j0 := eq2806 X0 X1
       grind)
    | exact resolve eq2806 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq2806
  have eq3148 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2847 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2847
    | (have j0 := eq2847 X1 (σ X0)
       grind)
    | exact resolve eq2847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847
  have eq3226 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3148 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3148
    | (have j0 := eq3148 X0 X1
       grind)
    | exact resolve eq3148 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3148
  have eq3233 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3226 X0 X1
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq3226
    | (have j0 := eq3226 X0 X1
       grind)
    | exact resolve eq3226 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3226
  have eq3236 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3233 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3233
    | (have j0 := eq3233 X0 X1
       grind)
    | exact resolve eq3233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3233
  have eq3710 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2755 x y
       grind)
    | exact superpose eq2755 eq16
    | (have j1 := eq2755 x y
       grind)
    | exact resolve eq16 eq2755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755
  have eq3785 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3710
       have i₂ := eq3236 y x
       grind)
    | exact superpose eq3236 eq3710
    | (have j1 := eq3236 x y
       grind)
    | (have r₁ := eq3710
       have r₂ := eq3236 y x
       grind)
    | exact resolve eq3710 eq3236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236 eq3710
  have eq3786 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3785
  have eq3818 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y y
       have i₂ := eq3786
       grind)
    | exact superpose eq3786 eq61
    | exact resolve eq61 eq3786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3819 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq3786
       grind)
    | exact superpose eq3786 eq61
    | exact resolve eq61 eq3786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3786
  have eq3839 : (M.op x x) = (M.op y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67 x (M.op x y) x
       have i₂ := eq3818 x
       grind)
    | exact superpose eq3818 eq67
    | exact resolve eq67 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq3818
  have eq3873 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3819 x
       have i₂ := eq3839
       grind)
    | exact superpose eq3839 eq3819
    | exact resolve eq3819 eq3839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819 eq3839
  have eq3894 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3873
  have eq3895 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3894
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq3894
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq3894
    | exact resolve eq3894 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3894
  have eq3896 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3895
       grind)
    | exact superpose eq3895 eq16
    | exact resolve eq16 eq3895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3895
  have eq3897 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq3896
       have r₂ := eq396 x
       grind)
    | exact resolve eq3896 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq3927 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq396 (M.op y y)
       have i₂ := eq3897
       grind)
    | exact superpose eq3897 eq396
    | exact resolve eq396 eq3897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897
  have eq3968 : (σ (M.op (M.op y y) (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq3927
       have i₂ := eq396 (M.op x x)
       grind)
    | exact superpose eq396 eq3927
    | exact resolve eq3927 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3927
  have eq3986 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq3968
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq3968
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq3968
    | exact resolve eq3968 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968
  have eq3987 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3986
       have i₂ := eq61 y y y
       grind)
    | (have i₁ := eq3986
       have i₂ := eq61 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq61 eq3986
    | exact resolve eq3986 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq3986
  have eq3988 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3987
       grind)
    | exact superpose eq3987 eq16
    | exact resolve eq16 eq3987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3989 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3987
       grind)
    | exact superpose eq3987 eq10
    | exact resolve eq10 eq3987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3987
  have eq4064 : x = y := by
    first
    | (have i₁ := eq3989
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3989
    | exact resolve eq3989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989
  have eq4065 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3988
       have i₂ := eq396 x
       grind)
    | exact superpose eq396 eq3988
    | exact resolve eq3988 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq3988
  have eq4066 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4065
       have i₂ := eq4064
       grind)
    | exact superpose eq4064 eq4065
    | exact resolve eq4065 eq4064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4064 eq4065
  have eq4067 : False := by grind
  exact eq4067
