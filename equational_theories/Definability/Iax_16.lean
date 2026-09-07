import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3398`: `x ◇ y = z ◇ (y ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3398 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3398 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3398.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X0 X2))) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X1 (M.op X0 X2)) (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X1 (M.op X0 X2))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
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
  have eq46 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq19 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X2 X1) X0
       have i₂ := eq19 X2 X0 X1
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 (M.op X1 X2)
       have i₂ := eq19 X1 (M.op X0 (M.op X1 X2)) X2
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq55 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq69 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq28 X1 (τ X0)
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X1 (τ X0)
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq102 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X0 (M.op X3 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X3 X0 X2 (M.op X3 X1)
       have i₂ := eq19 X3 X0 X1
       grind)
    | exact superpose eq19 eq18
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq114 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X1 (M.op X3 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq102 x X1 X2 X3
       have i₂ := eq19 x X1 (M.op X3 X2)
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq102
  have eq128 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq142 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq128 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq128
    | exact resolve eq128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq244 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq246 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq254 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq255 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq13
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq281 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq246 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq246
    | (have j0 := eq246 X0
       grind)
    | exact resolve eq246 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq471 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X2 X1
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq8 X2 X2 X1
       have i₂ := eq50 X2 X1 X0
       grind)
    | exact superpose eq50 eq8
    | exact resolve eq8 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq471 X2 x X0
       have i₂ := eq8 X2 X2 x
       grind)
    | exact superpose eq8 eq471
    | exact resolve eq471 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq555 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 X3 X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq51 X0 X1 X2
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq560 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X0 (M.op X1 (M.op X2 X3))) X3
       have i₂ := eq51 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq51 eq8
    | exact resolve eq8 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq555 X0 X1 X2 X3
       have i₂ := eq114 X1 (M.op X0 (M.op X1 X2)) X0
       grind)
    | (have i₁ := eq555 X0 X1 X2 X3
       have i₂ := eq114 (M.op X0 (M.op X1 X2)) X1 X0
       grind)
    | exact superpose eq114 eq555
    | exact resolve eq555 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq555
  have eq585 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq562 X0 x X2 X3
       have i₂ := eq560 X0 X0 x X2
       grind)
    | exact superpose eq560 eq562
    | exact resolve eq562 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq562
  have eq646 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq488 X1 X0
       grind)
    | (have i₁ := eq12 X1 X2
       have i₂ := eq488 X0 X1
       grind)
    | exact superpose eq488 eq12
    | (have j0 := eq12 X0 X2
       grind)
    | exact resolve eq12 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 X1
       have i₂ := eq488 X1 X0
       grind)
    | (have i₁ := eq70 X1 X1
       have i₂ := eq488 X0 X1
       grind)
    | exact superpose eq488 eq70
    | (have j0 := eq70 X1 X1
       grind)
    | (have r₁ := eq70 (M.op x x) (M.op x x)
       have r₂ := eq488 (M.op x x) x
       grind)
    | (have r₁ := eq70 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq488 X0 (M.op X0 X0)
       grind)
    | exact resolve eq70 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 X1
       have i₂ := eq488 (σ X1) X0
       grind)
    | (have i₁ := eq142 X1
       have i₂ := eq488 X0 (σ X1)
       grind)
    | exact superpose eq488 eq142
    | exact resolve eq142 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq7148 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq272 (M.op X0 X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq272
    | (have j0 := eq272 (M.op X0 X0)
       grind)
    | exact resolve eq272 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq7153 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq272 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq272
    | (have j0 := eq272 (τ X0)
       grind)
    | exact resolve eq272 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq7155 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq7148 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7148
  have eq7163 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7153 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7153
    | (have j0 := eq7153 X0
       grind)
    | exact resolve eq7153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7153
  have eq7170 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7163 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7163
    | (have j0 := eq7163 X0
       grind)
    | exact resolve eq7163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7163
  have eq15100 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq244
       have i₂ := eq646 X0 x y
       grind)
    | exact superpose eq646 eq244
    | (have j1 := eq646 (σ x) x (σ y)
       grind)
    | exact resolve eq244 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq646
  have eq15104 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq15100 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15100
  have eq15279 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (k (τ X0) (τ X0))
       have i₂ := eq281 (τ X0)
       grind)
    | exact superpose eq281 eq16
    | (have j1 := eq281 (τ X0)
       grind)
    | exact resolve eq16 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq15313 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15279 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq15279
    | (have j0 := eq15279 X0
       grind)
    | exact resolve eq15279 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15279
  have eq15331 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15313 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15313
    | (have j0 := eq15313 X0
       grind)
    | exact resolve eq15313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15313
  have eq15339 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15331 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15331
    | (have j0 := eq15331 X0
       grind)
    | exact resolve eq15331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15331
  have eq22572 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq669 (σ x) X0
       have i₂ := eq15104 X1
       grind)
    | exact superpose eq15104 eq669
    | (have j1 := eq15104 X1
       grind)
    | exact resolve eq669 eq15104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15104
  have eq22861 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22572 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq22572
    | (have j0 := eq22572 X0 X1
       grind)
    | exact resolve eq22572 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22572
  have eq24586 : ∀ X0 : G, y = (k y y) ∨ y = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq15339 y
       have i₂ := eq22861 y X0
       grind)
    | exact superpose eq22861 eq15339
    | (have j0 := eq15339 y
       have j1 := eq22861 y y
       grind)
    | exact resolve eq15339 eq22861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15339 eq22861
  have eq24818 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq24586 X0
       have j1 := eq70 y y
       grind)
    | (have r₁ := eq24586 X0
       have r₂ := eq70 y y
       grind)
    | (have r₁ := eq24586 y
       have r₂ := eq70 y y
       grind)
    | exact resolve eq24586 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq24586
  have eq24861 : y = (k y y) := by
    first
    | (have j1 := eq660 x y
       grind)
    | (have r₁ := eq24818 x
       have r₂ := eq660 x y
       grind)
    | exact resolve eq24818 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq24818
  have eq28252 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq24861
       grind)
    | exact superpose eq24861 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq24861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24861
  have eq28257 : y = (M.op y y) := by grind
  clear eq28252
  have eq28456 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq488 X0 y
       have i₂ := eq28257
       grind)
    | exact superpose eq28257 eq488
    | exact resolve eq488 eq28257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq28458 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq585 y X1 X0
       have i₂ := eq28257
       grind)
    | exact superpose eq28257 eq585
    | exact resolve eq585 eq28257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq28463 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq669 y X0
       have i₂ := eq28257
       grind)
    | exact superpose eq28257 eq669
    | exact resolve eq669 eq28257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq28257
  have eq30014 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ y = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X0 X0
       have i₂ := eq28456 X0
       grind)
    | exact superpose eq28456 eq46
    | (have j0 := eq46 X1 X0 x
       grind)
    | exact resolve eq46 eq28456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq30112 : ∀ X0 : G, y = (σ (k X0 X0)) ∨ (τ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq254 X0 X0
       have i₂ := eq28456 (σ X0)
       grind)
    | exact superpose eq28456 eq254
    | exact resolve eq254 eq28456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq31839 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq7170 (τ y)
       have i₂ := eq28463 (τ y)
       grind)
    | exact superpose eq28463 eq7170
    | (have j0 := eq7170 (τ y)
       grind)
    | (have r₁ := eq7170 (τ y)
       have r₂ := eq28463 (τ y)
       grind)
    | exact resolve eq7170 eq28463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7170 eq28463
  have eq31861 : (τ y) = (M.op (τ y) (τ y)) := by grind
  clear eq31839
  have eq31874 : y = (τ y) := by
    first
    | (have i₁ := eq31861
       have i₂ := eq28456 (τ y)
       grind)
    | exact superpose eq28456 eq31861
    | exact resolve eq31861 eq28456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31861
  have eq33683 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq31874
       grind)
    | exact superpose eq31874 eq10
    | exact resolve eq10 eq31874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33684 : ∀ X0 : G, (k y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq31874
       grind)
    | exact superpose eq31874 eq16
    | exact resolve eq16 eq31874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34874 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33683
       grind)
    | exact superpose eq33683 eq14
    | exact resolve eq14 eq33683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76052 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq255 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq255
    | exact resolve eq255 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq76528 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76052 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq76052
    | (have j0 := eq76052 X0 X1 X2
       grind)
    | exact resolve eq76052 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq76052
  have eq76903 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k y (σ X2)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76528 X0 X1 X2
       have i₂ := eq28456 X0
       grind)
    | exact superpose eq28456 eq76528
    | (have j0 := eq76528 X0 X1 X2
       grind)
    | exact resolve eq76528 eq28456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76528
  have eq77150 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (σ (k y X2)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76903 X0 X1 X2
       have i₂ := eq33684 X2
       grind)
    | exact superpose eq33684 eq76903
    | (have j0 := eq76903 X0 X1 X2
       grind)
    | exact resolve eq76903 eq33684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76903
  have eq114120 : ∀ X0 : G, (k X0 X0) = (τ y) ∨ (τ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0)
       have i₂ := eq30112 X0
       grind)
    | exact superpose eq30112 eq9
    | (have j1 := eq30112 (k X0 X0)
       grind)
    | exact resolve eq9 eq30112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30112
  have eq114218 : ∀ X0 : G, y = (k X0 X0) ∨ (τ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq114120 X0
       have i₂ := eq31874
       grind)
    | exact superpose eq31874 eq114120
    | (have j0 := eq114120 X0
       grind)
    | exact resolve eq114120 eq31874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114120
  have eq114310 : ∀ X0 : G, y = (k X0 X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq114218 X0
       have i₂ := eq31874
       grind)
    | exact superpose eq31874 eq114218
    | (have j0 := eq114218 X0
       grind)
    | exact resolve eq114218 eq31874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31874 eq114218
  have eq229127 : ∀ X0 : G, (k X0 (σ (τ X0))) = (M.op (k X0 (σ (τ X0))) (k X0 (σ (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7155 (τ X0)
       have i₂ := eq69 X0 (τ X0)
       grind)
    | exact superpose eq69 eq7155
    | (have j1 := eq69 X0 (τ X0)
       grind)
    | exact resolve eq7155 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq7155
  have eq229359 : ∀ X0 : G, y = (k X0 (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq229127 X0
       have i₂ := eq28456 (k X0 (σ (τ X0)))
       grind)
    | exact superpose eq28456 eq229127
    | (have j0 := eq229127 X0
       grind)
    | exact resolve eq229127 eq28456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28456 eq229127
  have eq229477 : ∀ X0 : G, y = (k X0 X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq229359 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq229359
    | (have j0 := eq229359 X0
       grind)
    | exact resolve eq229359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229359
  have eq229534 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq229477 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq229477
    | (have j0 := eq229477 X0
       grind)
    | exact resolve eq229477 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229477
  have eq229642 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq229534 X0
       grind)
    | exact superpose eq229534 eq10
    | (have j1 := eq229534 X0
       grind)
    | exact resolve eq10 eq229534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229534
  have eq229666 : ∀ X0 : G, (k X0 X0) = X0 ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq229642 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq229642
    | (have j0 := eq229642 X0
       grind)
    | exact resolve eq229642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229642
  have eq230583 : ∀ X0 : G, y ≠ X0 ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq229666 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229666
  have eq230595 : ∀ X0 : G, y = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq230583 X0
       have j1 := eq114310 X0
       grind)
    | (have r₁ := eq230583 (k X0 X0)
       have r₂ := eq114310 X0
       grind)
    | (have r₁ := eq230583 X0
       have r₂ := eq114310 X0
       grind)
    | (have r₁ := eq230583 y
       have r₂ := eq114310 y
       grind)
    | exact resolve eq230583 eq114310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114310 eq230583
  have eq368348 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (σ (k y (τ X1))) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77150 X2 (τ X0) (τ X1)
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq77150
    | (have j0 := eq77150 X2 (τ X0) X2
       grind)
    | exact resolve eq77150 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq77150
  have eq368580 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ y) X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368348 X0 X1 X2
       have i₂ := eq17 X1 y
       grind)
    | exact superpose eq17 eq368348
    | (have j0 := eq368348 X0 X1 X2
       grind)
    | exact resolve eq368348 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq368348
  have eq368659 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k y X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368580 X0 X1 X2
       have i₂ := eq33683
       grind)
    | exact superpose eq33683 eq368580
    | (have j0 := eq368580 X0 X1 X2
       grind)
    | exact resolve eq368580 eq33683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33683 eq368580
  have eq368706 : ∀ X0 X1 X2 : G, (k X0 X1) = (k y X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368659 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq368659
    | (have j0 := eq368659 X0 X1 X2
       grind)
    | exact resolve eq368659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368659
  have eq368724 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (k X0 X1) = (k y X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368706 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq368706
    | (have j0 := eq368706 X0 X1 X2
       grind)
    | exact resolve eq368706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368706
  have eq477194 : ∀ X0 : G, (k X0 X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq368724 X0 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368724
  have eq477198 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq477194 X0
       have i₂ := eq230595 X0
       grind)
    | exact superpose eq230595 eq477194
    | (have j0 := eq477194 X0
       grind)
    | exact resolve eq477194 eq230595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230595 eq477194
  have eq477564 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq477198 X0
       have j1 := eq30014 y X0
       grind)
    | (have r₁ := eq477198 x
       have r₂ := eq30014 X0 x
       grind)
    | exact resolve eq477198 eq30014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30014 eq477198
  have eq478017 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq33684 X0
       have i₂ := eq477564 (σ X0)
       grind)
    | exact superpose eq477564 eq33684
    | exact resolve eq33684 eq477564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33684
  have eq478290 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq478017 X0
       have i₂ := eq477564 X0
       grind)
    | exact superpose eq477564 eq478017
    | exact resolve eq478017 eq477564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477564 eq478017
  have eq478856 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq478290 (M.op y X0)
       have i₂ := eq28458 y X0
       grind)
    | exact superpose eq28458 eq478290
    | exact resolve eq478290 eq28458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479183 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (M.op y (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq478856 X0
       have i₂ := eq478290 X0
       grind)
    | exact superpose eq478290 eq478856
    | exact resolve eq478856 eq478290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478290 eq478856
  have eq479311 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq479183 X0
       have i₂ := eq28458 y (σ X0)
       grind)
    | exact superpose eq28458 eq479183
    | exact resolve eq479183 eq28458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28458 eq479183
  have eq480373 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq34874
       have i₂ := eq479311 x
       grind)
    | exact superpose eq479311 eq34874
    | (have r₁ := eq34874
       have r₂ := eq479311 x
       grind)
    | exact resolve eq34874 eq479311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34874 eq479311
  have eq480429 : False := by grind
  exact eq480429

/-- `Equation3417`: `x ◇ y = z ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3417 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3417 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X1 X0))) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X1 X0)) X2) = (M.op X3 (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 (M.op X1 X0)) X2 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X0) X2 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1 X2
       have i₂ := eq19 (M.op X1 X0) X2 X2
       grind)
    | (have i₁ := eq20 X0 X1 (M.op X0 X1)
       have i₂ := eq19 X0 X1 (M.op (M.op X0 X1) (M.op X1 X0))
       grind)
    | exact superpose eq19 eq20
    | exact resolve eq20 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq23 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
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
  have eq27 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X1 X0) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 X0 (M.op X2 X3)
       have i₂ := eq19 X3 X2 (M.op X1 X0)
       grind)
    | (have i₁ := eq19 X0 X1 X2
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq26
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op X1 X0)
       have i₂ := eq21 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq119 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq90 X2 (M.op X0 X1)
       grind)
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq90 (M.op X0 X1) X2
       grind)
    | exact superpose eq90 eq8
    | exact resolve eq8 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq128 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq132 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq27 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq178 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq41
  have eq193 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq178
    | exact resolve eq178 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq226 : ∀ X0 X1 X2 : G, (M.op X2 X1) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128 (M.op X2 X1) X0
       have i₂ := eq19 X1 X2 X0
       grind)
    | (have i₁ := eq128 X2 (M.op X0 X1)
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq128
    | (have j0 := eq128 (M.op X2 X1) X0
       grind)
    | exact resolve eq128 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq235 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq33
    | (have j0 := eq33 X1 X0
       have j1 := eq33 X1 X0
       grind)
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
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
  have eq250 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq259 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X1) (σ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq90
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq90 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq278 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq339 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq193 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq193 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq193
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq193 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1779 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    grind
  clear eq55
  have eq2800 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq278 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq278
    | (have j0 := eq278 (τ X0)
       grind)
    | exact resolve eq278 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq2802 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2800 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2800
    | (have j0 := eq2800 X0
       grind)
    | exact resolve eq2800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2800
  have eq2805 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2802 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2802
    | (have j0 := eq2802 X0
       grind)
    | exact resolve eq2802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802
  have eq2818 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2805 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq2805
    | (have j0 := eq2805 (τ X0)
       grind)
    | exact resolve eq2805 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq2805
  have eq2829 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 X0
       have i₂ := eq90 X1 (τ X0)
       grind)
    | (have i₁ := eq36 X1 X0
       have i₂ := eq90 (τ X0) X1
       grind)
    | exact superpose eq90 eq36
    | (have j0 := eq36 X1 X0
       grind)
    | exact resolve eq36 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2852 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq2974 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2852 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2852
    | (have j0 := eq2852 X0 X1
       grind)
    | exact resolve eq2852 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq3489 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq122 X0 X0
       grind)
    | exact superpose eq122 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq122 X0 X0
       grind)
    | exact resolve eq12 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq4021 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq250
       have i₂ := eq2974 y x
       grind)
    | exact superpose eq2974 eq250
    | (have j1 := eq2974 (σ y) (σ x)
       grind)
    | (have r₁ := eq250
       have r₂ := eq2974 y x
       grind)
    | exact resolve eq250 eq2974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4022 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq4021
  have eq4035 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq193 x
       have i₂ := eq4022
       grind)
    | exact superpose eq4022 eq193
    | exact resolve eq193 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4080 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4035
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4035
    | exact resolve eq4035 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035
  have eq4160 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq4080
       grind)
    | exact superpose eq4080 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq4080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4164 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2974 y x
       have i₂ := eq4080
       grind)
    | exact superpose eq4080 eq2974
    | (have j0 := eq2974 y x
       grind)
    | exact resolve eq2974 eq4080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974 eq4080
  have eq4165 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq4164
  have eq4166 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq4160
  have eq5675 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq261 x x
       have i₂ := eq4022
       grind)
    | exact superpose eq4022 eq261
    | exact resolve eq261 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq5753 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5675
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5675
    | exact resolve eq5675 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5675
  have eq9781 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X1) (σ X0)
       have i₂ := eq235 X1 X0
       grind)
    | exact superpose eq235 eq90
    | (have j1 := eq235 X1 X0
       grind)
    | exact resolve eq90 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq17283 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq278 (τ X0)
       have i₂ := eq132 (τ X0) X0
       grind)
    | exact superpose eq132 eq278
    | (have j0 := eq278 (τ X0)
       have j1 := eq132 (τ X0) X0
       grind)
    | exact resolve eq278 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq17338 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq17283 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17283
    | (have j0 := eq17283 X0
       grind)
    | exact resolve eq17283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17283
  have eq17370 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq17338 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17338
    | (have j0 := eq17338 X0
       grind)
    | exact resolve eq17338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17338
  have eq17392 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq17370 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17370
    | (have j0 := eq17370 X0
       grind)
    | exact resolve eq17370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17370
  have eq17408 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq17392 X0
       have j1 := eq128 X0 X0
       grind)
    | (have r₁ := eq17392 x
       have r₂ := eq128 x x
       grind)
    | exact resolve eq17392 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17392
  have eq18122 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq17408 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq17408
    | (have j0 := eq17408 (σ X0)
       grind)
    | exact resolve eq17408 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17408
  have eq18160 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18122 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq18122
    | (have j0 := eq18122 X0
       grind)
    | exact resolve eq18122 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18122
  have eq28513 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2829 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2829
    | exact resolve eq2829 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829
  have eq28950 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28513 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq28513
    | (have j0 := eq28513 X0 X1
       grind)
    | exact resolve eq28513 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28513
  have eq29196 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq28950 X0 X1
       grind)
    | exact superpose eq28950 eq9
    | (have j1 := eq28950 X0 X1
       grind)
    | exact resolve eq9 eq28950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29305 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  clear eq28950
  have eq29514 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29196 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq29196
    | (have j0 := eq29196 X0 X1
       grind)
    | exact resolve eq29196 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29196
  have eq30278 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq43920 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X1
       have i₂ := eq259 X1 X0
       grind)
    | exact superpose eq259 eq193
    | (have j1 := eq259 X1 X0
       grind)
    | exact resolve eq193 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq259
  have eq44065 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43920 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43920
    | (have j0 := eq43920 X0 X1
       grind)
    | exact resolve eq43920 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43920
  have eq66593 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2818 (σ X0)
       have i₂ := eq339 (σ X0) X0
       grind)
    | exact superpose eq339 eq2818
    | (have j0 := eq2818 (σ X0)
       have j1 := eq339 (σ X0) X0
       grind)
    | exact resolve eq2818 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq2818
  have eq66627 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq66593 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66593
    | (have j0 := eq66593 X0
       grind)
    | exact resolve eq66593 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66593
  have eq66641 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq66627 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66627
    | (have j0 := eq66627 X0
       grind)
    | exact resolve eq66627 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66627
  have eq66647 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq66641 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66641
    | (have j0 := eq66641 X0
       grind)
    | exact resolve eq66641 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66641
  have eq66651 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq66647 X0
       have j1 := eq128 X0 X0
       grind)
    | (have r₁ := eq66647 x
       have r₂ := eq128 x x
       grind)
    | exact resolve eq66647 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq66647
  have eq67275 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66651 x
       have i₂ := eq4022
       grind)
    | exact superpose eq4022 eq66651
    | (have j0 := eq66651 x
       grind)
    | exact resolve eq66651 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66651
  have eq67316 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq67275
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq67275
    | exact resolve eq67275 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67275
  have eq91529 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44065 x y
       grind)
    | exact superpose eq44065 eq14
    | (have j1 := eq44065 x y
       grind)
    | exact resolve eq14 eq44065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44065
  have eq91813 : y = (k y x) := by
    first
    | (have j1 := eq29305 x y
       grind)
    | (have r₁ := eq91529
       have r₂ := eq29305 x y
       grind)
    | exact resolve eq91529 eq29305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29305 eq91529
  have eq93746 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29514 x y
       have i₂ := eq91813
       grind)
    | exact superpose eq91813 eq29514
    | (have j0 := eq29514 x y
       grind)
    | exact resolve eq29514 eq91813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29514
  have eq107157 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq5753
       grind)
    | exact superpose eq5753 eq9
    | exact resolve eq9 eq5753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5753
  have eq107167 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq107157
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq107157
    | exact resolve eq107157 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107157
  have eq107225 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30278 x x
       have i₂ := eq107167
       grind)
    | exact superpose eq107167 eq30278
    | exact resolve eq30278 eq107167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30278 eq107167
  have eq107228 : y = (M.op x x) ∨ x = y := by grind
  clear eq107225
  have eq107309 : ∀ X0 : G, y = (M.op X0 (M.op y X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq119 x x x
       have i₂ := eq107228
       grind)
    | exact superpose eq107228 eq119
    | exact resolve eq119 eq107228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107228
  have eq107472 : y = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107309 y
       have i₂ := eq93746
       grind)
    | exact superpose eq93746 eq107309
    | exact resolve eq107309 eq93746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107596 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (M.op X0 y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq226 X0 y X0
       have i₂ := eq107309 X0
       grind)
    | exact superpose eq107309 eq226
    | (have j0 := eq226 X0 y X0
       grind)
    | exact resolve eq226 eq107309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq107309
  have eq108123 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107472
       have i₂ := eq90 y x
       grind)
    | (have i₁ := eq107472
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq107472
    | exact resolve eq107472 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107472
  have eq108124 : y = (M.op x y) ∨ x = y := by grind
  clear eq108123
  have eq108340 : (M.op y x) = (k (M.op y x) (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq1779 x y
       have i₂ := eq108124
       grind)
    | exact superpose eq108124 eq1779
    | exact resolve eq1779 eq108124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779 eq108124
  have eq108385 : (M.op x y) = (k (M.op x y) (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq108340
       have i₂ := eq90 y x
       grind)
    | (have i₁ := eq108340
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq108340
    | exact resolve eq108340 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108340
  have eq131769 : (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108385
       have i₂ := eq93746
       grind)
    | exact superpose eq93746 eq108385
    | exact resolve eq108385 eq93746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108385
  have eq131771 : (M.op x y) = (k (M.op x y) x) ∨ x = y := by
    first
    | (have j1 := eq107596 x
       grind)
    | (have r₁ := eq131769
       have r₂ := eq107596 x
       grind)
    | exact resolve eq131769 eq107596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107596 eq131769
  have eq131837 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq131771
       have i₂ := eq4166
       grind)
    | exact superpose eq4166 eq131771
    | exact resolve eq131771 eq4166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166 eq131771
  have eq131865 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq131837
       have r₂ := eq67316
       grind)
    | exact resolve eq131837 eq67316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67316 eq131837
  have eq131993 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq278 x
       have i₂ := eq131865
       grind)
    | exact superpose eq131865 eq278
    | (have j0 := eq278 x
       grind)
    | exact resolve eq278 eq131865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq131865
  have eq132032 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq131993
  have eq134685 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq119 (σ x) (σ x) x
       have i₂ := eq132032
       grind)
    | exact superpose eq132032 eq119
    | exact resolve eq119 eq132032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132032
  have eq135568 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq134685 (σ x)
       have i₂ := eq4022
       grind)
    | exact superpose eq4022 eq134685
    | exact resolve eq134685 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022 eq134685
  have eq135784 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq135568
  have eq135866 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq135784
       grind)
    | exact superpose eq135784 eq14
    | exact resolve eq14 eq135784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135784
  have eq135976 : y = (M.op x x) := by
    first
    | (have r₁ := eq135866
       have r₂ := eq4165
       grind)
    | exact resolve eq135866 eq4165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4165 eq135866
  have eq136002 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq18160 x
       have i₂ := eq135976
       grind)
    | exact superpose eq135976 eq18160
    | (have j0 := eq18160 x
       grind)
    | exact resolve eq18160 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18160
  have eq136043 : ∀ X0 : G, y = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq119 x x x
       have i₂ := eq135976
       grind)
    | exact superpose eq135976 eq119
    | exact resolve eq119 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136225 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq136043 y
       have i₂ := eq93746
       grind)
    | exact superpose eq93746 eq136043
    | exact resolve eq136043 eq93746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93746 eq136043
  have eq137181 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq136225
       have i₂ := eq90 y x
       grind)
    | (have i₁ := eq136225
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq136225
    | exact resolve eq136225 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq136225
  have eq137182 : y = (M.op x y) := by grind
  clear eq137181
  have eq148561 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3489 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3489
  have eq148562 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq148561 X0 X1
       have j1 := eq236 X1 X0
       grind)
    | (have r₁ := eq148561 (k X1 X1) X0
       have r₂ := eq236 X0 X1
       grind)
    | (have r₁ := eq148561 X0 (σ (k X1 X1))
       have r₂ := eq236 (σ X0) X1
       grind)
    | (have r₁ := eq148561 X1 X0
       have r₂ := eq236 X0 X1
       grind)
    | exact resolve eq148561 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq148561
  have eq148592 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq148562 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq148562 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq148562 eq16
    | (have j1 := eq148562 (τ X1) X0
       grind)
    | exact resolve eq16 eq148562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148562
  have eq148613 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq148592 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq148592
    | (have j0 := eq148592 X0 X1
       grind)
    | exact resolve eq148592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148592
  have eq148619 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq148613 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148613
    | (have j0 := eq148613 X0 X1
       grind)
    | exact resolve eq148613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148613
  have eq148820 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (τ X1))) ∨ (M.op (τ X1) X0) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq148619 X0 (τ X1)
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq148619 (k (τ X0) X1) X1
       grind)
    | exact superpose eq148619 eq16
    | (have j1 := eq148619 X0 (τ X1)
       grind)
    | exact resolve eq16 eq148619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq148619
  have eq148851 : ∀ X0 X1 : G, (σ X0) = (k X1 X1) ∨ (M.op (τ X1) X0) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq148820 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq148820
    | (have j0 := eq148820 X0 X1
       grind)
    | exact resolve eq148820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148820
  have eq151641 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k (τ (σ X1)) X0) = (M.op (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq148851 X0 (σ X1)
       grind)
    | exact superpose eq148851 eq13
    | (have j1 := eq148851 X0 (σ X1)
       grind)
    | exact resolve eq13 eq148851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148851
  have eq151659 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq151641 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq151641
    | (have j0 := eq151641 X0 X1
       grind)
    | exact resolve eq151641 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151641
  have eq151884 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9781 y x
       grind)
    | exact superpose eq9781 eq14
    | (have j1 := eq9781 y x
       grind)
    | exact resolve eq14 eq9781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9781
  have eq151886 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151884
       have i₂ := eq91813
       grind)
    | exact superpose eq91813 eq151884
    | exact resolve eq151884 eq91813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91813 eq151884
  have eq151888 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151886
       have i₂ := eq137182
       grind)
    | exact superpose eq137182 eq151886
    | exact resolve eq151886 eq137182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151886
  have eq151889 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq151888
  have eq151921 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq151889
       grind)
    | exact superpose eq151889 eq9
    | exact resolve eq9 eq151889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151889
  have eq151937 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151921
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq151921
    | exact resolve eq151921 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151921
  have eq152016 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151659 y y
       have i₂ := eq151937
       grind)
    | exact superpose eq151937 eq151659
    | exact resolve eq151659 eq151937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151659 eq151937
  have eq152017 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq152016
  have eq152125 : ∀ X0 : G, x = (M.op X0 (M.op x X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq119 y y x
       have i₂ := eq152017
       grind)
    | exact superpose eq152017 eq119
    | exact resolve eq119 eq152017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq152017
  have eq152321 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq152125 x
       have i₂ := eq135976
       grind)
    | exact superpose eq135976 eq152125
    | exact resolve eq152125 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152125
  have eq152929 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq152321
       have i₂ := eq137182
       grind)
    | exact superpose eq137182 eq152321
    | exact resolve eq152321 eq137182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137182 eq152321
  have eq153009 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq152929
       grind)
    | exact superpose eq152929 eq9
    | exact resolve eq9 eq152929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152929
  have eq153085 : x = y ∨ x = y := by
    first
    | (have i₁ := eq153009
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq153009
    | exact resolve eq153009 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153009
  have eq153086 : x = y := by grind
  clear eq153085
  have eq153092 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq153086
       grind)
    | exact superpose eq153086 eq14
    | exact resolve eq14 eq153086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153093 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq250
       have i₂ := eq153086
       grind)
    | exact superpose eq153086 eq250
    | exact resolve eq250 eq153086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq153160 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq136002
       have i₂ := eq153086
       grind)
    | exact superpose eq153086 eq136002
    | exact resolve eq136002 eq153086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136002
  have eq153180 : (σ x) = (σ (k x x)) := by grind
  clear eq153160
  have eq153199 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153093
       have i₂ := eq135976
       grind)
    | exact superpose eq135976 eq153093
    | exact resolve eq153093 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153093
  have eq153200 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153092
       have i₂ := eq135976
       grind)
    | exact superpose eq135976 eq153092
    | exact resolve eq153092 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135976 eq153092
  have eq153206 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153199
       have i₂ := eq153180
       grind)
    | exact superpose eq153180 eq153199
    | exact resolve eq153199 eq153180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153180 eq153199
  have eq153207 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153200
       have i₂ := eq153086
       grind)
    | exact superpose eq153086 eq153200
    | exact resolve eq153200 eq153086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153200
  have eq153208 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153206
       have i₂ := eq153086
       grind)
    | exact superpose eq153086 eq153206
    | exact resolve eq153206 eq153086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153086 eq153206
  have eq153209 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq153208
  have eq153210 : False := by grind
  exact eq153210

/-- `Equation3470`: `x ◇ x = x ◇ ((y ◇ z) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3470 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3470 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3470.models_iff G M).mp hM
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq220 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq226 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq220 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq220 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq220 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq220 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq226 (σ X0) (σ X1)
       grind)
    | exact superpose eq226 eq13
    | exact resolve eq13 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X0 X1
       have i₂ := eq226 X0 X1
       grind)
    | exact superpose eq226 eq249
    | exact resolve eq249 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq249
  have eq1841 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq260 x y
       grind)
    | exact superpose eq260 eq14
    | (have r₁ := eq14
       have r₂ := eq260 x y
       grind)
    | exact resolve eq14 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq1871 : False := by grind
  exact eq1871

/-- `Equation3471`: `x ◇ x = y ◇ ((x ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyy_pxy_pyx_Equation3471 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3471 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3471.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq13
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq39
    | exact resolve eq39 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq39
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq68
    | (have j0 := eq68 X0 X1
       grind)
    | exact resolve eq68 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq150 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X1)
       have i₂ := eq74 X0 X1
       grind)
    | (have i₁ := eq9 (M.op X0 X0)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq9
    | (have j1 := eq74 X0 X1
       grind)
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq382 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq370
    | (have j0 := eq370 X0 X1
       grind)
    | exact resolve eq370 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1001 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1134 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1601 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq1001 (σ X0) (σ X1)
       grind)
    | exact superpose eq1001 eq13
    | (have j1 := eq1001 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1610 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1601 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1601
    | (have j0 := eq1601 X0 X1
       grind)
    | exact resolve eq1601 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1849 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1134 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1134
    | exact resolve eq1134 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq3596 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq382 x y
       grind)
    | exact superpose eq382 eq14
    | (have j1 := eq382 x y
       grind)
    | exact resolve eq14 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq10973 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3596
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq3596
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq3596 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10981 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq3596
       have i₂ := eq1001 x y
       grind)
    | exact superpose eq1001 eq3596
    | (have j1 := eq1001 x y
       grind)
    | exact resolve eq3596 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq3596
  have eq10983 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq10981
  have eq10990 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq10973
  have eq10991 : (M.op x x) = (M.op y y) := by grind
  clear eq10990
  have eq10992 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq11 x y
       grind)
    | (have r₁ := eq10983
       have r₂ := eq11 x y
       grind)
    | (have r₁ := eq10983
       have r₂ := eq11 y x
       grind)
    | exact resolve eq10983 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10983
  have eq11457 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq11 y X0
       have i₂ := eq10991
       grind)
    | exact superpose eq10991 eq11
    | (have j0 := eq11 X0 x
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq10991
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq10991
       grind)
    | exact resolve eq11 eq10991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17363 : (k y x) = (M.op y x) := by
    first
    | (have j0 := eq11457 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11457
  have eq46873 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq150 y X0
       have i₂ := eq10991
       grind)
    | exact superpose eq10991 eq150
    | (have j0 := eq150 x X0
       grind)
    | exact resolve eq150 eq10991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq10991
  have eq108680 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq46873 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq46873
    | (have j0 := eq46873 (σ X0)
       grind)
    | (have r₁ := eq46873 (σ x)
       have r₂ := eq42 x
       grind)
    | exact resolve eq46873 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq46873
  have eq108790 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq108680 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq108680
    | (have j0 := eq108680 X0
       grind)
    | exact resolve eq108680 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108680
  have eq469435 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1610 x y
       grind)
    | exact superpose eq1610 eq14
    | (have j1 := eq1610 x y
       grind)
    | exact resolve eq14 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq469440 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq469435
       have i₂ := eq17363
       grind)
    | exact superpose eq17363 eq469435
    | exact resolve eq469435 eq17363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469435
  have eq469445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq469440
       have i₂ := eq10992
       grind)
    | exact superpose eq10992 eq469440
    | exact resolve eq469440 eq10992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469440
  have eq469450 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have r₁ := eq469445
       have r₂ := eq14
       grind)
    | exact resolve eq469445 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469445
  have eq480057 : (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have j0 := eq108790 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108790
  have eq480059 : (σ (M.op y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq480057
       have i₂ := eq17363
       grind)
    | exact superpose eq17363 eq480057
    | exact resolve eq480057 eq17363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17363 eq480057
  have eq480085 : (σ (M.op y x)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1849 x y
       have i₂ := eq480059
       grind)
    | exact superpose eq480059 eq1849
    | (have j0 := eq1849 x y
       grind)
    | exact resolve eq1849 eq480059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849 eq480059
  have eq480123 : (σ (M.op x y)) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq480085
       have i₂ := eq10992
       grind)
    | exact superpose eq10992 eq480085
    | exact resolve eq480085 eq10992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480085
  have eq480141 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq480123
       have r₂ := eq469450
       grind)
    | exact resolve eq480123 eq469450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469450 eq480123
  have eq480154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq480141
       have i₂ := eq10992
       grind)
    | exact superpose eq10992 eq480141
    | exact resolve eq480141 eq10992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10992 eq480141
  have eq480164 : False := by grind
  exact eq480164

/-- `Equation3487`: `x ◇ x = y ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation3487 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3487 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3487.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op (M.op X2 x) X0)
       have i₂ := eq8 X0 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq45 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq45 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X2 X3 (M.op (M.op X2 X2) X3)
       have i₂ := eq23 X1 (M.op (M.op X2 X2) X3) X0
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X2 X3) (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X1 X1) X0) X2 X3
       have i₂ := eq23 X1 X0 (M.op (M.op X1 X1) X0)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X1 X1) X0) X2 x
       have i₂ := eq23 X1 X0 (M.op X2 x)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq92 X0 x X2
       have i₂ := eq23 x X0 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq23 eq92
    | exact resolve eq92 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq92
  have eq98 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X1 X2
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq93
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq93 X0 (M.op X0 X0)
       grind)
    | exact superpose eq93 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq93 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq151 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq169 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X2 X3) X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X2 X3
       have i₂ := eq111 X1 X0
       grind)
    | exact superpose eq111 eq8
    | exact resolve eq8 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (M.op X2 (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X1 X2
       have i₂ := eq111 X0 X1
       grind)
    | exact superpose eq111 eq93
    | exact resolve eq93 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq2139 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq151 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq2176 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq2139 (σ X0)
       grind)
    | exact superpose eq2139 eq13
    | exact resolve eq13 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2178 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq2139 (τ X0)
       grind)
    | exact superpose eq2139 eq35
    | exact resolve eq35 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2181 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2178 X0
       have i₂ := eq2139 X0
       grind)
    | exact superpose eq2139 eq2178
    | exact resolve eq2178 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq2183 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2176 X0
       have i₂ := eq2139 X0
       grind)
    | exact superpose eq2139 eq2176
    | exact resolve eq2176 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139 eq2176
  have eq2637 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) x
       have i₂ := eq2181 X0
       grind)
    | exact superpose eq2181 eq93
    | exact resolve eq93 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181
  have eq2751 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) x
       have i₂ := eq2183 X0
       grind)
    | exact superpose eq2183 eq93
    | exact resolve eq93 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3501 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq3663 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3501 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3501
    | (have j0 := eq3501 X0 X1
       grind)
    | exact resolve eq3501 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3501
  have eq6475 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X2 x (M.op x x) X0
       have i₂ := eq169 X0 X1 (M.op x x) (M.op x x)
       grind)
    | exact superpose eq169 eq80
    | exact resolve eq80 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq169
  have eq8404 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X1 (τ (σ X0))) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2637 (σ X1) X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq2637
    | (have j1 := eq49 X2 X0
       grind)
    | exact resolve eq2637 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq2637
  have eq8574 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8404 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq8404
    | (have j0 := eq8404 X0 X1 X2
       grind)
    | exact resolve eq8404 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8404
  have eq9284 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2751 X0 X1
       have i₂ := eq98 X0 X0 X2
       grind)
    | exact superpose eq98 eq2751
    | (have j1 := eq98 (σ X0) X1 X2
       grind)
    | exact resolve eq2751 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq2751
  have eq10923 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X2 X3) (M.op X0 X0))) = (M.op (k X0 (M.op X1 X1)) (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq90 (k X0 (M.op X1 X1)) x X2 X3
       have i₂ := eq6475 X0 X1 (M.op x x)
       grind)
    | exact superpose eq6475 eq90
    | exact resolve eq90 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq6475
  have eq10960 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X1 X1)) = (M.op X2 (M.op (M.op X2 X3) (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10923 X0 X1 X2 X3
       have i₂ := eq175 X0 X1 (k X0 (M.op X1 X1))
       grind)
    | exact superpose eq175 eq10923
    | exact resolve eq10923 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq10923
  have eq11147 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10960 X0 X1 X2 x
       have i₂ := eq93 X0 (M.op X2 x)
       grind)
    | (have i₁ := eq10960 x X1 x x
       have i₂ := eq93 (M.op x x) X2
       grind)
    | exact superpose eq93 eq10960
    | exact resolve eq10960 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10960
  have eq17581 : ∀ X0 X1 X2 : G, (k (σ X0) (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11147 (σ X0) X2 X1
       have i₂ := eq2183 X0
       grind)
    | exact superpose eq2183 eq11147
    | exact resolve eq11147 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17692 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 X0))) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11147 X2 (σ X0) X1
       have i₂ := eq2183 X0
       grind)
    | exact superpose eq2183 eq11147
    | exact resolve eq11147 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11147
  have eq68233 : ∀ X0 X1 X2 : G, (k (σ X0) (σ (M.op X1 X1))) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17692 X1 X2 (σ X0)
       have i₂ := eq2183 X0
       grind)
    | exact superpose eq2183 eq17692
    | exact resolve eq17692 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183 eq17692
  have eq68930 : ∀ X0 X1 X2 : G, (σ (k X0 (M.op X1 X1))) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68233 X0 X1 X2
       have i₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact superpose eq13 eq68233
    | exact resolve eq68233 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68233
  have eq257551 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X1 X2
       have i₂ := eq3663 X0 X1
       grind)
    | exact superpose eq3663 eq93
    | (have j1 := eq3663 X2 X0
       grind)
    | exact resolve eq93 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq3663
  have eq297690 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq9284 y (σ x) X0
       grind)
    | exact superpose eq9284 eq14
    | (have j1 := eq9284 y x X0
       grind)
    | exact resolve eq14 eq9284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9284
  have eq438727 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq8574 y X0 x
       grind)
    | exact superpose eq8574 eq14
    | (have j1 := eq8574 y X0 x
       grind)
    | exact resolve eq14 eq8574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8574
  have eq438747 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq438727 X0
       have j1 := eq257551 y X0 x
       grind)
    | (have r₁ := eq438727 X0
       have r₂ := eq257551 y x x
       grind)
    | exact resolve eq438727 eq257551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257551 eq438727
  have eq439111 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (k (σ X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq17581 X0 X1 y
       have i₂ := eq438747 y
       grind)
    | exact superpose eq438747 eq17581
    | exact resolve eq17581 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17581
  have eq439239 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (σ (k X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq68930 X0 y X1
       have i₂ := eq438747 y
       grind)
    | exact superpose eq438747 eq68930
    | exact resolve eq68930 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68930
  have eq439854 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq297690 X0
       have i₂ := eq438747 x
       grind)
    | exact superpose eq438747 eq297690
    | (have j0 := eq297690 X0
       grind)
    | exact resolve eq297690 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297690
  have eq439855 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq439854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439854
  have eq439862 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq439855 X0
       have i₂ := eq438747 X0
       grind)
    | exact superpose eq438747 eq439855
    | exact resolve eq439855 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439855
  have eq440199 : ∀ X0 : G, (k (σ X0) y) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq439111 X0 x
       have i₂ := eq439239 X0 x
       grind)
    | exact superpose eq439239 eq439111
    | exact resolve eq439111 eq439239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439111 eq439239
  have eq440406 : ∀ X0 : G, (σ y) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq440199 X0
       have i₂ := eq439862 X0
       grind)
    | exact superpose eq439862 eq440199
    | exact resolve eq440199 eq439862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440199
  have eq440499 : y = (σ y) := by
    first
    | (have i₁ := eq440406 x
       have i₂ := eq439862 (σ x)
       grind)
    | exact superpose eq439862 eq440406
    | exact resolve eq440406 eq439862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439862 eq440406
  have eq440569 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq440499
       grind)
    | exact superpose eq440499 eq14
    | exact resolve eq14 eq440499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440723 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq440569
       have i₂ := eq438747 (σ x)
       grind)
    | exact superpose eq438747 eq440569
    | exact resolve eq440569 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440569
  have eq440782 : y ≠ (σ y) := by
    first
    | (have i₁ := eq440723
       have i₂ := eq438747 x
       grind)
    | exact superpose eq438747 eq440723
    | exact resolve eq440723 eq438747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438747 eq440723
  have eq440820 : False := by grind
  exact eq440820

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3495 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3495 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq169 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq175 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq169 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq169 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq169 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq197 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq175 (σ X0) (σ X1)
       grind)
    | exact superpose eq175 eq13
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 X1
       have i₂ := eq175 X0 X1
       grind)
    | exact superpose eq175 eq197
    | exact resolve eq197 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq197
  have eq1870 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq207 x y
       grind)
    | exact superpose eq207 eq14
    | (have r₁ := eq14
       have r₂ := eq207 x y
       grind)
    | exact resolve eq14 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1902 : False := by grind
  exact eq1902

/-- `Equation3503`: `x ◇ x = y ◇ ((z ◇ w) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation3503 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3503 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X4 (M.op (M.op X5 X6) X3)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq8 X3 X4 X5 X6
       have i₂ := eq8 X3 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) = (M.op X3 (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X1 X2) X0) X3 x x
       have i₂ := eq8 X0 (M.op x x) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op X3 (M.op X0 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq26 X0 x x X3
       have i₂ := eq8 X0 (M.op (M.op x x) X0) x x
       grind)
    | (have i₁ := eq26 X0 x x X3
       have i₂ := eq8 (M.op (M.op x x) X0) x x X3
       grind)
    | exact superpose eq8 eq26
    | exact resolve eq26 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq29 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X4 (M.op X0 (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq28 X0 X3
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq28
    | exact resolve eq28 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq28 X0 (M.op X0 X0)
       grind)
    | exact superpose eq28 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq28 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq53 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (M.op X1 X1)) = (M.op X2 (M.op (M.op X3 X4) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X2 X3 X4
       have i₂ := eq42 X1 X0
       grind)
    | exact superpose eq42 eq8
    | exact resolve eq8 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq68 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 X3) X0)) = X0 ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X1 X2 X3
       have i₂ := eq12 X4 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X4 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq73 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq75 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq75 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq117 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq166 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op (M.op X2 X3) (M.op (M.op X4 X5) X0))) = (M.op X6 (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq21 X1 X2 X3 (M.op (M.op X4 X5) X0) X6 x x
       have i₂ := eq8 X0 (M.op x x) X4 X5
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq204 : ∀ X0 X2 X3 X4 X5 X6 : G, (M.op (M.op X2 X3) (M.op (M.op X4 X5) X0)) = (M.op X6 (M.op X0 X0)) := by
    intro X0 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq166 X0 x X2 X3 X4 X5 X6
       have i₂ := eq29 (M.op X2 X3) X4 X5 X0 x
       grind)
    | exact superpose eq29 eq166
    | exact resolve eq166 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq166
  have eq2441 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq115 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq2476 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq2441 (σ X0)
       grind)
    | exact superpose eq2441 eq13
    | exact resolve eq13 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2478 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq117 X0 X0
       have i₂ := eq2441 (τ X0)
       grind)
    | exact superpose eq2441 eq117
    | exact resolve eq117 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq2481 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2478 X0
       have i₂ := eq2441 X0
       grind)
    | exact superpose eq2441 eq2478
    | exact resolve eq2478 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq2483 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2476 X0
       have i₂ := eq2441 X0
       grind)
    | exact superpose eq2441 eq2476
    | exact resolve eq2476 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441 eq2476
  have eq2971 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (τ X0) x
       have i₂ := eq2481 X0
       grind)
    | exact superpose eq2481 eq28
    | exact resolve eq28 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481
  have eq3089 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) x
       have i₂ := eq2483 X0
       grind)
    | exact superpose eq2483 eq28
    | exact resolve eq28 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3346 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73
    | (have j0 := eq73 X0 X1
       grind)
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq3518 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3346 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3346
    | (have j0 := eq3346 X0 X1
       grind)
    | exact resolve eq3346 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq4542 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X2 (M.op x x) x x
       have i₂ := eq204 X1 x x x x X0
       grind)
    | (have i₁ := eq53 (M.op x x) X1 x x x
       have i₂ := eq204 (M.op x x) X2 x x x x
       grind)
    | exact superpose eq204 eq53
    | exact resolve eq53 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq204
  have eq7087 : ∀ X0 X1 X2 : G, (k (σ X0) (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4542 X1 (σ X0) X2
       have i₂ := eq2483 X0
       grind)
    | exact superpose eq2483 eq4542
    | exact resolve eq4542 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7160 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4542 X1 X2 (σ X0)
       have i₂ := eq2483 X0
       grind)
    | exact superpose eq2483 eq4542
    | exact resolve eq4542 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4542
  have eq7758 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X1 (τ (σ X0))) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2971 (σ X1) X1
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq2971
    | (have j1 := eq72 X2 X0
       grind)
    | exact resolve eq2971 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2971
  have eq7891 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7758 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq7758
    | (have j0 := eq7758 X0 X1 X2
       grind)
    | exact resolve eq7758 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7758
  have eq8331 : ∀ X0 X3 X4 : G, (σ X0) = (M.op X3 (σ X0)) ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq3089 (M.op (M.op x X3) X0) x
       have i₂ := eq68 X0 (M.op (M.op x X3) X0) x X3 X4
       grind)
    | exact superpose eq68 eq3089
    | (have j1 := eq68 X0 x x X3 X4
       grind)
    | exact resolve eq3089 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq3089
  have eq38701 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7160 X2 X1 (σ X0)
       have i₂ := eq2483 X0
       grind)
    | exact superpose eq2483 eq7160
    | exact resolve eq7160 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483 eq7160
  have eq39388 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (σ (k X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38701 X0 X1 X2
       have i₂ := eq13 X0 (M.op X2 X2)
       grind)
    | exact superpose eq13 eq38701
    | exact resolve eq38701 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38701
  have eq168917 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 x
       have i₂ := eq3518 X0 X1
       grind)
    | exact superpose eq3518 eq28
    | (have j1 := eq3518 X2 X0
       grind)
    | exact resolve eq28 eq3518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3518
  have eq209793 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq8331 y (σ x) X0
       grind)
    | exact superpose eq8331 eq14
    | (have j1 := eq8331 y x X0
       grind)
    | exact resolve eq14 eq8331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8331
  have eq328534 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq7891 y X0 x
       grind)
    | exact superpose eq7891 eq14
    | (have j1 := eq7891 y X0 x
       grind)
    | exact resolve eq14 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7891
  have eq328598 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq328534 X0
       have j1 := eq168917 y X0 x
       grind)
    | (have r₁ := eq328534 X0
       have r₂ := eq168917 y x x
       grind)
    | exact resolve eq328534 eq168917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168917 eq328534
  have eq328878 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (k (σ X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq7087 X0 X1 y
       have i₂ := eq328598 y
       grind)
    | exact superpose eq328598 eq7087
    | exact resolve eq7087 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7087
  have eq329052 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = (σ (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq39388 X1 X0 y
       have i₂ := eq328598 y
       grind)
    | exact superpose eq328598 eq39388
    | exact resolve eq39388 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39388
  have eq329548 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq209793 X0
       have i₂ := eq328598 x
       grind)
    | exact superpose eq328598 eq209793
    | (have j0 := eq209793 X0
       grind)
    | exact resolve eq209793 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209793
  have eq329553 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq329548 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329548
  have eq329559 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq329553 X0
       have i₂ := eq328598 X0
       grind)
    | exact superpose eq328598 eq329553
    | exact resolve eq329553 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329553
  have eq329783 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq328878 X0 x
       have i₂ := eq329052 x X0
       grind)
    | exact superpose eq329052 eq328878
    | exact resolve eq328878 eq329052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328878 eq329052
  have eq329986 : ∀ X0 : G, y = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq329783 X0
       have i₂ := eq329559 (σ X0)
       grind)
    | exact superpose eq329559 eq329783
    | exact resolve eq329783 eq329559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329783
  have eq330101 : y = (σ y) := by
    first
    | (have i₁ := eq329986 x
       have i₂ := eq329559 x
       grind)
    | exact superpose eq329559 eq329986
    | exact resolve eq329986 eq329559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329559 eq329986
  have eq330436 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq330101
       grind)
    | exact superpose eq330101 eq14
    | exact resolve eq14 eq330101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330575 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq330436
       have i₂ := eq328598 (σ x)
       grind)
    | exact superpose eq328598 eq330436
    | exact resolve eq330436 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330436
  have eq330627 : y ≠ (σ y) := by
    first
    | (have i₁ := eq330575
       have i₂ := eq328598 x
       grind)
    | exact superpose eq328598 eq330575
    | exact resolve eq330575 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328598 eq330575
  have eq330669 : False := by grind
  exact eq330669

/-- `Equation3526`: `x ◇ y = x ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_pyy_pxx_pyx_Equation3526 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3526 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3526.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq13
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq38
    | exact resolve eq38 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq38
  have eq49 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq12 X2 X0
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X1 X0
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
  have eq58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq63 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq62
    | exact resolve eq62 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq62 (τ X0) X1
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 (τ X0) X1
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq62
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq185 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0) (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq8
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) X2) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq49 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq49 eq13
    | (have j1 := eq49 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq13 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2809 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
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
  have eq2976 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2809 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2809
    | (have j0 := eq2809 X0 X1
       grind)
    | exact resolve eq2809 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2809
  have eq3720 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0)
       have i₂ := eq108 X0 X1
       grind)
    | exact superpose eq108 eq9
    | (have j1 := eq108 X0 X1
       grind)
    | exact resolve eq9 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq3844 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3720 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq3720
    | (have j0 := eq3720 X0 X1
       grind)
    | exact resolve eq3720 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq10355 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3844 y x
       grind)
    | exact superpose eq3844 eq14
    | (have j1 := eq3844 y x
       grind)
    | exact resolve eq14 eq3844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3844
  have eq10453 : (k y x) = (M.op y y) := by
    first
    | (have j1 := eq2976 x y
       grind)
    | (have r₁ := eq10355
       have r₂ := eq2976 x y
       grind)
    | exact resolve eq10355 eq2976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976 eq10355
  have eq10912 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq10453
       grind)
    | exact superpose eq10453 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq10453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11238 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y y
       have i₂ := eq10912
       grind)
    | exact superpose eq10912 eq8
    | exact resolve eq8 eq10912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10912
  have eq11273 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq11238 X0
       have i₂ := eq8 X0 x y
       grind)
    | exact superpose eq8 eq11238
    | exact resolve eq11238 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11238
  have eq12744 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq11273 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11273
  have eq12745 : (M.op x y) = (M.op x x) := by grind
  clear eq12744
  have eq52442 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq525 x X0 (σ y)
       grind)
    | (have i₁ := eq14
       have i₂ := eq525 x y x
       grind)
    | exact superpose eq525 eq14
    | (have j1 := eq525 x X0 (σ y)
       grind)
    | exact resolve eq14 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq52783 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq52442 X0
       have i₂ := eq12745
       grind)
    | exact superpose eq12745 eq52442
    | (have j0 := eq52442 X0
       grind)
    | exact resolve eq52442 eq12745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52442
  have eq52932 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq52783 X0
       have j1 := eq63 x X0
       grind)
    | (have r₁ := eq52783 x
       have r₂ := eq63 x x
       grind)
    | exact resolve eq52783 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq52783
  have eq52991 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq52932 X0
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq52932
    | (have j0 := eq52932 y
       grind)
    | exact resolve eq52932 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52932
  have eq53014 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq52991 X0
       have i₂ := eq10453
       grind)
    | exact superpose eq10453 eq52991
    | (have j0 := eq52991 X0
       grind)
    | exact resolve eq52991 eq10453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52991
  have eq207546 : (σ (k y x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq53014
  have eq207547 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq207546
       have i₂ := eq10453
       grind)
    | exact superpose eq10453 eq207546
    | exact resolve eq207546 eq10453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10453 eq207546
  have eq207548 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq207547
  have eq207613 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op y y)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x) (σ y)
       have i₂ := eq207548
       grind)
    | exact superpose eq207548 eq8
    | exact resolve eq8 eq207548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207548
  have eq207648 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq207613 X0
       have i₂ := eq185 y X0
       grind)
    | exact superpose eq185 eq207613
    | exact resolve eq207613 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq207613
  have eq207967 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq207648 (σ x)
       grind)
    | exact superpose eq207648 eq14
    | exact resolve eq14 eq207648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207648
  have eq208105 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq207967
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq207967
    | exact resolve eq207967 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq207967
  have eq208329 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq208105
       have i₂ := eq12745
       grind)
    | exact superpose eq12745 eq208105
    | exact resolve eq208105 eq12745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12745 eq208105
  have eq208330 : False := by grind
  exact eq208330
