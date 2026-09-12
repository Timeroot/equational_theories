import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_x_pxx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq105 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq335 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq352 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq61 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq61 X2 X3 X0
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq64 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq61 X2 X3 X0
       grind)
    | exact superpose eq61 eq64
    | exact resolve eq64 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X4 x X2
       have i₂ := eq64 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq64 X2 X2 X2 x
       grind)
    | exact superpose eq64 eq14
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 x
       have i₂ := eq64 X0 X1 sF3 x
       grind)
    | (have i₁ := eq63 (M.op sF3 sF3)
       have i₂ := eq64 sF3 sF3 sF3 x
       grind)
    | exact superpose eq64 eq63
    | exact resolve eq63 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq64
  have eq665 : ∀ X0 X1 X3 : G, (M.op X1 X1) ≠ X0 ∨ (k X3 X0) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq65 X0 (M.op x (M.op (M.op X0 X0) (M.op X1 X1))) x
       have i₂ := eq61 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq61 eq65
    | (have r₁ := eq65 X0 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X1))) x
       have r₂ := eq61 (M.op X0 X0) X1 (M.op X0 X0)
       grind)
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq667 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X2 (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 (M.op X0 X0) X2
       have i₂ := eq352 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq65 X0 (M.op X0 X0) X2
       have i₂ := eq352 (M.op X0 X0) X1
       grind)
    | exact superpose eq352 eq65
    | (have r₁ := eq65 X1 (M.op X1 X1) X2
       have r₂ := eq352 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq65 X0 (M.op X0 X0) X2
       have r₂ := eq352 X0 (M.op X0 X0)
       grind)
    | exact resolve eq65 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq669 : ∀ X0 X2 : G, (k X2 (M.op X0 X0)) = X2 := by
    intro X0 X2
    first
    | (have j0 := eq667 X0 x X2
       grind)
    | (have r₁ := eq667 X0 x X2
       have r₂ := eq352 X0 x
       grind)
    | (have r₁ := eq667 x X0 X2
       have r₂ := eq352 X0 x
       grind)
    | exact resolve eq667 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq681 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 (M.op X1 X1)
       have i₂ := eq669 X1 (σ X0)
       grind)
    | exact superpose eq669 eq335
    | exact resolve eq335 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq682 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq681
    | exact resolve eq681 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq1442 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X0
       have i₂ := eq352 X0 (σ X0)
       grind)
    | (have i₁ := eq75 X0 X0
       have i₂ := eq352 (σ X0) X1
       grind)
    | exact superpose eq352 eq75
    | exact resolve eq75 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1478 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1479 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq1513 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1442 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442
  have eq5149 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X2 X3)) X2) (M.op X0 X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq464 X1 X2 X3 X3
       have i₂ := eq352 X0 X3
       grind)
    | (have i₁ := eq464 X1 X2 X3 X3
       have i₂ := eq352 X3 X0
       grind)
    | exact superpose eq352 eq464
    | exact resolve eq464 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq464
  have eq5302 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1479 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1479
    | (have j0 := eq1479 (τ X0)
       grind)
    | exact resolve eq1479 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1479
  have eq5320 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5302 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5302
    | (have j0 := eq5302 X0
       grind)
    | exact resolve eq5302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5302
  have eq5330 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5320 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5320
    | (have j0 := eq5320 X0
       grind)
    | exact resolve eq5320 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5320
  have eq7166 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X2 (M.op (M.op X0 X2) (M.op X3 X3)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq444 X2 X1 (M.op X0 X2) X3 x
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq444
    | exact resolve eq444 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7199 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq355 X1 x X2 x
       have i₂ := eq444 X1 x X2 x X0
       grind)
    | exact superpose eq444 eq355
    | exact resolve eq355 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq7772 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7199 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq355 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq355 eq7199
    | exact resolve eq7199 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq8685 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7772 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7772
    | (have j0 := eq7772 x X0 y
       grind)
    | exact resolve eq7772 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31087 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1513 X1 (M.op X0 X0)
       have i₂ := eq669 X0 (M.op X0 X0)
       grind)
    | exact superpose eq669 eq1513
    | (have j0 := eq1513 X1 (M.op X0 X0)
       grind)
    | exact resolve eq1513 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq31470 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31087 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31087
  have eq31933 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq31470 X1 X0
       grind)
    | exact superpose eq31470 eq16
    | exact resolve eq16 eq31470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31470
  have eq32105 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq31933 X2 x
       have i₂ := eq31933 X0 x
       grind)
    | exact superpose eq31933 eq31933
    | exact resolve eq31933 eq31933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32294 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq8685 x
       have i₂ := eq31933 X0 x
       grind)
    | exact superpose eq31933 eq8685
    | exact resolve eq8685 eq31933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8685
  have eq34070 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (τ (τ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq32105 x X2
       have i₂ := eq31933 X0 x
       grind)
    | exact superpose eq31933 eq32105
    | exact resolve eq32105 eq31933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32105
  have eq46499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq46500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq46499
    | exact resolve eq46499 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46499
  have eq46511 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq46500
       have r₂ := eq28
       grind)
    | exact resolve eq46500 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46500
  have eq46573 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq46511 eq682
    | exact resolve eq682 eq46511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq46511
  have eq46705 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30 eq46573
    | exact resolve eq46573 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46573
  have eq46712 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq46705 X0
       have j1 := eq665 y x X0
       grind)
    | (have r₁ := eq46705 (M.op x x)
       have r₂ := eq665 (k (M.op x x) y) x x
       grind)
    | (have r₁ := eq46705 X0
       have r₂ := eq665 (σ y) (σ x) x
       grind)
    | (have r₁ := eq46705 X0
       have r₂ := eq665 y x x
       grind)
    | exact resolve eq46705 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46705
  have eq46714 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq46712 X0
       have j1 := eq665 y x X0
       grind)
    | (have r₁ := eq46712 (M.op x x)
       have r₂ := eq665 (k (M.op x x) y) x x
       grind)
    | (have r₁ := eq46712 X0
       have r₂ := eq665 (σ y) (σ x) x
       grind)
    | (have r₁ := eq46712 X0
       have r₂ := eq665 y y x
       grind)
    | exact resolve eq46712 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46712
  have eq46837 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ y)) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31933 X0 X1
       have i₂ := eq46714 (M.op X0 X0)
       grind)
    | exact superpose eq46714 eq31933
    | (have j1 := eq46714 X1
       grind)
    | exact resolve eq31933 eq46714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31933 eq46714
  have eq46903 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | exact superpose eq30 eq46837
    | (have j0 := eq46837 X0 X1
       grind)
    | exact resolve eq46837 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46837
  have eq46916 : ∀ X1 : G, (k X1 y) = X1 := by
    intro X1
    first
    | (have j0 := eq46903 x X1
       have j1 := eq665 y X1 X1
       grind)
    | (have r₁ := eq46903 X1 X1
       have r₂ := eq665 y X1 x
       grind)
    | (have r₁ := eq46903 x (M.op X1 X1)
       have r₂ := eq665 (k (M.op X1 X1) y) X1 x
       grind)
    | exact resolve eq46903 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq46903
  have eq46977 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1513 X0 y
       have i₂ := eq46916 y
       grind)
    | exact superpose eq46916 eq1513
    | (have j0 := eq1513 X0 y
       grind)
    | exact resolve eq1513 eq46916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq46983 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5330 y
       have i₂ := eq46916 y
       grind)
    | exact superpose eq46916 eq5330
    | (have j0 := eq5330 y
       grind)
    | (have r₁ := eq5330 y
       have r₂ := eq46916 y
       grind)
    | exact resolve eq5330 eq46916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5330 eq46916
  have eq47009 : y = (M.op y y) := by grind
  clear eq46983
  have eq47014 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq46977 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46977
  have eq47041 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq47014 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq47014
    | (have j0 := eq47014 X0
       grind)
    | exact resolve eq47014 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47014
  have eq47130 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 y X0
       have i₂ := eq47009
       grind)
    | exact superpose eq47009 eq14
    | exact resolve eq14 eq47009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47133 : x = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq62 y
       have i₂ := eq47009
       grind)
    | exact superpose eq47009 eq62
    | exact resolve eq62 eq47009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq47225 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7199 y X0 X1
       have i₂ := eq47009
       grind)
    | exact superpose eq47009 eq7199
    | exact resolve eq7199 eq47009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47323 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq47133
       have i₂ := eq47009
       grind)
    | exact superpose eq47009 eq47133
    | exact resolve eq47133 eq47009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47133
  have eq49126 : y = (σ y) := by
    first
    | (have i₁ := eq47041 y
       have i₂ := eq47009
       grind)
    | exact superpose eq47009 eq47041
    | exact resolve eq47041 eq47009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47009
  have eq49300 : ∀ X1 : G, (τ (σ y)) = (τ (τ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq34070 X1 x
       have i₂ := eq47041 x
       grind)
    | exact superpose eq47041 eq34070
    | exact resolve eq34070 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34070
  have eq49386 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq468 sF3 sF3
       have i₂ := eq47041 (M.op sF3 sF3)
       grind)
    | exact superpose eq47041 eq468
    | exact resolve eq468 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq49394 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq47041 (M.op X0 X0)
       grind)
    | exact superpose eq47041 eq14
    | exact resolve eq14 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49414 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7199 X0 (M.op X0 X0) X1
       have i₂ := eq47041 (M.op X0 X0)
       grind)
    | exact superpose eq47041 eq7199
    | exact resolve eq7199 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7199
  have eq49449 : ∀ X1 : G, (M.op (M.op (σ y) X1) (σ y)) = X1 := by
    intro X1
    first
    | (have i₁ := eq49414 x X1
       have i₂ := eq47041 x
       grind)
    | exact superpose eq47041 eq49414
    | exact resolve eq49414 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49414
  have eq49468 : ∀ X1 : G, (M.op (σ y) (M.op X1 (σ y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq49394 x X1
       have i₂ := eq47041 x
       grind)
    | exact superpose eq47041 eq49394
    | exact resolve eq49394 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49394
  have eq49474 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq49386
       have i₂ := eq47041 sF3
       grind)
    | exact superpose eq47041 eq49386
    | exact resolve eq49386 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49386
  have eq49543 : (τ (σ y)) = (τ (τ (σ y))) := by
    first
    | (have i₁ := eq49300 x
       have i₂ := eq47041 x
       grind)
    | exact superpose eq47041 eq49300
    | exact resolve eq49300 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49300
  have eq49744 : y = (τ y) := by
    first
    | exact superpose eq30 eq49543
    | exact resolve eq49543 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49543
  have eq53264 : (σ x) = (M.op y (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq49126 eq49474
    | exact resolve eq49474 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49474
  have eq53666 : ∀ X1 : G, (M.op (M.op y X1) y) = X1 := by
    intro X1
    first
    | exact superpose eq49126 eq49449
    | exact resolve eq49449 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49449
  have eq53667 : ∀ X1 : G, (M.op y (M.op X1 y)) = X1 := by
    intro X1
    first
    | exact superpose eq49126 eq49468
    | exact resolve eq49468 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49468
  have eq54316 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X2 X3)) X2) (σ y)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq5149 x X1 X2 X3
       have i₂ := eq47041 x
       grind)
    | exact superpose eq47041 eq5149
    | exact resolve eq5149 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq54317 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X2 X3)) X2) y) = X3 := by
    intro X1 X2 X3
    first
    | exact superpose eq49126 eq54316
    | exact resolve eq54316 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54316
  have eq54318 : ∀ X2 X3 : G, (M.op (M.op (M.op (σ y) (M.op X2 X3)) X2) y) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq54317 x X2 X3
       have i₂ := eq47041 x
       grind)
    | exact superpose eq47041 eq54317
    | exact resolve eq54317 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54317
  have eq54319 : ∀ X2 X3 : G, (M.op (M.op (M.op y (M.op X2 X3)) X2) y) = X3 := by
    intro X2 X3
    first
    | exact superpose eq49126 eq54318
    | exact resolve eq54318 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54318
  have eq56495 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op (M.op X0 X2) (σ y)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7166 X0 X1 X2 x
       have i₂ := eq47041 x
       grind)
    | exact superpose eq47041 eq7166
    | exact resolve eq7166 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7166
  have eq56496 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op (M.op X0 X2) y))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq49126 eq56495
    | exact resolve eq56495 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56495
  have eq56497 : ∀ X0 X2 : G, (M.op (σ y) (M.op X2 (M.op (M.op X0 X2) y))) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq56496 X0 x X2
       have i₂ := eq47041 x
       grind)
    | exact superpose eq47041 eq56496
    | exact resolve eq56496 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56496
  have eq56498 : ∀ X0 X2 : G, (M.op y (M.op X2 (M.op (M.op X0 X2) y))) = X0 := by
    intro X0 X2
    first
    | exact superpose eq49126 eq56497
    | exact resolve eq56497 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56497
  have eq56701 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) y) y) = (M.op X1 (M.op (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq54319 y (M.op X1 (M.op (M.op X0 X1) y))
       have i₂ := eq56498 X0 X1
       grind)
    | exact superpose eq56498 eq54319
    | exact resolve eq54319 eq56498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56498
  have eq56702 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (M.op (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq56701 X0 X1
       have i₂ := eq53666 X0
       grind)
    | (have i₁ := eq56701 X0 X1
       have i₂ := eq53666 (M.op (M.op y X0) y)
       grind)
    | exact superpose eq53666 eq56701
    | exact resolve eq56701 eq53666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53666 eq56701
  have eq57677 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq53264 eq47130
    | exact resolve eq47130 eq53264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47130 eq53264
  have eq59903 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq57677 eq7772
    | exact resolve eq7772 eq57677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7772 eq57677
  have eq82533 : ∀ X0 : G, (M.op (M.op X0 y) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) y) := by
    intro X0
    first
    | (have i₁ := eq59903 (M.op (M.op X0 sF2) y)
       have i₂ := eq56702 X0 sF2
       grind)
    | exact superpose eq56702 eq59903
    | exact resolve eq59903 eq56702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56702 eq59903
  have eq124755 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq47323 eq105
    | exact resolve eq105 eq47323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq47323
  have eq124756 : (σ x) = (k y (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq49126 eq124755
    | exact resolve eq124755 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124755
  have eq124757 : (σ x) = (k y (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq124756
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq124756
    | exact resolve eq124756 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124756
  have eq124758 : (M.op x y) = (σ y) ∨ (σ x) = (k y (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq124757
       have i₂ := eq47041 y
       grind)
    | exact superpose eq47041 eq124757
    | exact resolve eq124757 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124757
  have eq124759 : y = (M.op x y) ∨ (σ x) = (k y (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq49126 eq124758
    | exact resolve eq124758 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124758
  have eq124760 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (k y (σ (M.op x y))) := by
    first
    | (have i₁ := eq124759
       have i₂ := eq47041 sF0
       grind)
    | exact superpose eq47041 eq124759
    | exact resolve eq124759 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124759
  have eq124761 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (k y (σ (M.op x y))) := by
    first
    | exact superpose eq49126 eq124760
    | exact resolve eq124760 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124760
  have eq124762 : (σ x) = (k y (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq124761
  have eq124769 : (σ x) = (M.op y (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq124762 eq11
    | (have j0 := eq11 y (σ (M.op x y))
       grind)
    | exact resolve eq11 eq124762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124762
  have eq124770 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op y (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124769
       have i₂ := eq47041 y
       grind)
    | exact superpose eq47041 eq124769
    | exact resolve eq124769 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124769
  have eq124775 : y = (σ (M.op x y)) ∨ (σ x) = (M.op y (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49126 eq124770
    | exact resolve eq124770 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124770
  have eq124779 : (σ (M.op x y)) = (σ y) ∨ y = (σ (M.op x y)) ∨ (σ x) = (M.op y (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124775
       have i₂ := eq47041 sF1
       grind)
    | exact superpose eq47041 eq124775
    | exact resolve eq124775 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124775
  have eq124783 : y = (σ (M.op x y)) ∨ y = (σ (M.op x y)) ∨ (σ x) = (M.op y (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49126 eq124779
    | exact resolve eq124779 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124779
  have eq124784 : (σ x) = (M.op y (σ (M.op x y))) ∨ y = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq124783
  have eq124895 : (σ (M.op x y)) = (M.op (M.op (M.op y (σ x)) y) y) ∨ y = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq124784 eq54319
    | exact resolve eq54319 eq124784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54319 eq124784
  have eq124907 : (σ (M.op x y)) = (M.op (M.op (M.op y y) (M.op (σ x) (σ y))) y) ∨ y = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq82533 eq124895
    | exact resolve eq124895 eq82533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82533 eq124895
  have eq124931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124907
       have i₂ := eq47225 y sF4
       grind)
    | exact superpose eq47225 eq124907
    | exact resolve eq124907 eq47225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47225 eq124907
  have eq124953 : y = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq124931
       have r₂ := eq28
       grind)
    | exact resolve eq124931 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124931
  have eq125025 : (M.op x y) = (τ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq124953 eq31
    | exact resolve eq31 eq124953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq124953
  have eq125224 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq125025
       have i₂ := eq49744
       grind)
    | exact superpose eq49744 eq125025
    | exact resolve eq125025 eq49744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49744 eq125025
  have eq125225 : y = (M.op x y) := by grind
  clear eq125224
  have eq125344 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq125225 eq21
    | exact resolve eq21 eq125225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq125438 : ∀ X0 : G, y = (M.op y (M.op x (τ (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq125225 eq32294
    | exact resolve eq32294 eq125225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32294
  have eq125516 : y = (M.op y (M.op x (τ (σ y)))) := by
    first
    | (have i₁ := eq125438 x
       have i₂ := eq47041 x
       grind)
    | exact superpose eq47041 eq125438
    | exact resolve eq125438 eq47041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47041 eq125438
  have eq125598 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq125344
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq125344
    | exact resolve eq125344 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125344
  have eq125612 : y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq30 eq125516
    | exact resolve eq125516 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq125516
  have eq125690 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq49126 eq125598
    | exact resolve eq125598 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125598
  have eq125698 : x = y := by
    first
    | (have i₁ := eq125612
       have i₂ := eq53667 x
       grind)
    | (have i₁ := eq125612
       have i₂ := eq53667 (M.op y (M.op x y))
       grind)
    | exact superpose eq53667 eq125612
    | exact resolve eq125612 eq53667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53667 eq125612
  have eq126146 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq125698
       grind)
    | exact superpose eq125698 eq25
    | exact resolve eq25 eq125698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq126422 : y = (σ x) := by
    first
    | exact superpose eq49126 eq126146
    | exact resolve eq126146 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126146
  have eq126526 : y = (σ x) := by
    first
    | (have i₁ := eq126422
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq126422
    | exact resolve eq126422 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq126422
  have eq126609 : x = (σ x) := by
    first
    | (have i₁ := eq126526
       have i₂ := eq125698
       grind)
    | exact superpose eq125698 eq126526
    | exact resolve eq126526 eq125698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126526
  have eq128816 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq126609 eq27
    | exact resolve eq27 eq126609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq126609
  have eq129051 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49126 eq128816
    | exact resolve eq128816 eq49126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49126 eq128816
  have eq129120 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq129051
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq129051
    | exact resolve eq129051 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq129051
  have eq129174 : y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq125225 eq129120
    | exact resolve eq129120 eq125225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125225 eq129120
  have eq129222 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq129174
       have i₂ := eq125698
       grind)
    | exact superpose eq125698 eq129174
    | exact resolve eq129174 eq125698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129174
  have eq129316 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq129222 eq28
    | exact resolve eq28 eq129222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq129222
  have eq129382 : x ≠ y := by
    first
    | exact superpose eq125690 eq129316
    | exact resolve eq129316 eq125690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125690 eq129316
  have eq129412 : False := by grind
  exact eq129412

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
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
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq61
    | exact resolve eq61 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq61
  have eq81 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq97 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq91
  have eq550 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq97 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq555 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq550 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq559 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq555 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq555 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq555 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq567 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq559 X0 X1
       have j1 := eq81 X1 (σ X0)
       grind)
    | (have r₁ := eq559 X0 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq559 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq559
  have eq572 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq567
    | (have j0 := eq567 X0 X1
       grind)
    | exact resolve eq567 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq573 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq572 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq775 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq573 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq573
    | exact resolve eq573 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq573 x y
       grind)
    | exact superpose eq573 eq16
    | exact resolve eq16 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq1955 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq775 X0 (τ X1)
       grind)
    | exact superpose eq775 eq18
    | exact resolve eq18 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq775
  have eq1972 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1955 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1955
    | exact resolve eq1955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq1991 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1972 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1972
    | exact resolve eq1972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972
  have eq2254 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq796
       have i₂ := eq1991 x y
       grind)
    | exact superpose eq1991 eq796
    | exact resolve eq796 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq1991
  have eq2255 : False := by grind
  exact eq2255

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_x_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq175 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq558 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X1 X0
       grind)
    | exact superpose eq538 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq538 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq538 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq538 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq538 X2 X0
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq558 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq956 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq563 X2 X1 X0
       have i₂ := eq929 X0 X1
       grind)
    | exact superpose eq929 eq563
    | exact resolve eq563 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962 : ∀ X0 : G, x = (M.op (k y (M.op X0 X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq929 y X0
       grind)
    | exact superpose eq929 eq176
    | exact resolve eq176 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq963 : ∀ X0 : G, (σ x) = (M.op (k (σ y) (M.op X0 X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq177 x
       have i₂ := eq929 sF3 x
       grind)
    | exact superpose eq929 eq177
    | exact resolve eq177 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1441 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1442 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1474 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1475 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1535 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1536 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1537 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq2386 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1474
       grind)
    | exact superpose eq1474 eq40
    | exact resolve eq40 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq2387 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2386
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2386
    | exact resolve eq2386 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386
  have eq2389 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2387
    | exact resolve eq2387 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq2855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2389 eq1475
    | exact resolve eq1475 eq2389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2862 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2855
       have r₂ := eq27
       grind)
    | exact resolve eq2855 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2855
  have eq2880 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2862 eq538
    | exact resolve eq538 eq2862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq3045 : ∀ X0 : G, (σ y) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq929 (M.op X0 X0) X0
       have i₂ := eq2880 (M.op X0 X0)
       grind)
    | exact superpose eq2880 eq929
    | exact resolve eq929 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3057 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2880 eq3045
    | exact resolve eq3045 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2880 eq3045
  have eq3163 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3057 eq152
    | exact resolve eq152 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057
  have eq3168 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq3163
    | exact resolve eq3163 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3163
  have eq3171 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1537 y
       grind)
    | (have r₁ := eq3168
       have r₂ := eq1537 y
       grind)
    | exact resolve eq3168 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168
  have eq3184 : x = (M.op (M.op y y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq176 y
       have i₂ := eq3171
       grind)
    | exact superpose eq3171 eq176
    | exact resolve eq176 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3189 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq538 y X0
       have i₂ := eq3171
       grind)
    | exact superpose eq3171 eq538
    | exact resolve eq538 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3247 : x = (k (M.op x y) (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3184
       have i₂ := eq929 sF0 y
       grind)
    | exact superpose eq929 eq3184
    | exact resolve eq3184 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3184
  have eq3261 : x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3171 eq3247
    | exact resolve eq3247 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3171 eq3247
  have eq3348 : ∀ X0 : G, y = (k (M.op X0 X0) (M.op X0 X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq929 (M.op X0 X0) X0
       have i₂ := eq3189 (M.op X0 X0)
       grind)
    | exact superpose eq3189 eq929
    | exact resolve eq929 eq3189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3364 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3189 eq3348
    | exact resolve eq3348 eq3189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq3453 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3261 eq40
    | exact resolve eq40 eq3261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq3454 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3453
    | exact resolve eq3453 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3453
  have eq3456 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3454
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3454
    | exact resolve eq3454 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454
  have eq3459 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq3364
       grind)
    | exact superpose eq3364 eq40
    | exact resolve eq40 eq3364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq3464 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3459
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3459
    | exact resolve eq3459 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3459
  have eq3478 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3464 eq1537
    | (have j0 := eq1537 (σ y)
       grind)
    | (have r₁ := eq1537 (σ y)
       have r₂ := eq3464
       grind)
    | exact resolve eq1537 eq3464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3464
  have eq3479 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3478
  have eq4065 : ∀ X0 X1 : G, (M.op (k X0 (M.op X1 X1)) (σ y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq3479 eq956
    | exact resolve eq956 eq3479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq4082 : y = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3479 eq3189
    | exact resolve eq3189 eq3479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479
  have eq4086 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (σ y) := by grind
  clear eq4082
  have eq4102 : ∀ X0 : G, (M.op (k X0 y) (σ y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3189 eq4065
    | exact resolve eq4065 eq3189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3189 eq4065
  have eq4130 : ∀ X0 : G, (M.op (k X0 (σ y)) (σ y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4086 eq4102
    | exact resolve eq4102 eq4086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086 eq4102
  have eq5649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3456 eq4130
    | exact resolve eq4130 eq3456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3456 eq4130
  have eq5668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5649
  have eq5674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5668
    | exact resolve eq5668 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668
  have eq5679 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5674
       have r₂ := eq27
       grind)
    | exact resolve eq5674 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5674
  have eq5683 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5679 eq27
    | exact resolve eq27 eq5679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5687 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5679 eq1442
    | (have r₁ := eq1442
       have r₂ := eq5679
       grind)
    | exact resolve eq1442 eq5679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442
  have eq5689 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5687
  have eq6195 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5689 eq177
    | exact resolve eq177 eq5689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6277 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6195
       have i₂ := eq929 sF4 sF3
       grind)
    | exact superpose eq929 eq6195
    | exact resolve eq6195 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6195
  have eq6295 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5689 eq6277
    | exact resolve eq6277 eq5689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5689 eq6277
  have eq6301 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5679 eq6295
    | exact resolve eq6295 eq5679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5679 eq6295
  have eq6302 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6301
  have eq6308 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6302 eq2389
    | exact resolve eq2389 eq6302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq6313 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6302 eq152
    | exact resolve eq152 eq6302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6302
  have eq6318 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq6308
  have eq6322 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq6313
    | exact resolve eq6313 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6313
  have eq6325 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6318
       have r₂ := eq5683
       grind)
    | exact resolve eq6318 eq5683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5683 eq6318
  have eq6357 : x = (M.op (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq176 y
       have i₂ := eq6325
       grind)
    | exact superpose eq6325 eq176
    | exact resolve eq176 eq6325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6364 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq538 y X0
       have i₂ := eq6325
       grind)
    | exact superpose eq6325 eq538
    | exact resolve eq538 eq6325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6369 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) y) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq563 y X0 X1
       have i₂ := eq6325
       grind)
    | exact superpose eq6325 eq563
    | exact resolve eq563 eq6325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6401 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (M.op X1 X1) y) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq178 y X1 y X0
       have i₂ := eq6325
       grind)
    | exact superpose eq6325 eq178
    | exact resolve eq178 eq6325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6417 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op (k y (M.op X1 X1)) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq6401 X0 X1
       have i₂ := eq929 y X1
       grind)
    | exact superpose eq929 eq6401
    | exact resolve eq6401 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6401
  have eq6434 : ∀ X0 X1 : G, (M.op (k X1 (M.op X0 X0)) y) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq6369 X0 X1
       have i₂ := eq929 X1 X0
       grind)
    | exact superpose eq929 eq6369
    | exact resolve eq6369 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6369
  have eq6442 : x = (k (M.op x y) (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6357
       have i₂ := eq929 sF0 y
       grind)
    | exact superpose eq929 eq6357
    | exact resolve eq6357 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6357
  have eq6444 : ∀ X0 X1 : G, (k y (M.op X0 X0)) = (M.op (k y (M.op X1 X1)) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq6417 X0 X1
       have i₂ := eq929 y X0
       grind)
    | exact superpose eq929 eq6417
    | exact resolve eq6417 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6417
  have eq6451 : ∀ X1 : G, (M.op (k X1 y) y) = X1 ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq6364 eq6434
    | exact resolve eq6434 eq6364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6434
  have eq6459 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6325 eq6442
    | exact resolve eq6442 eq6325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6325 eq6442
  have eq6460 : ∀ X0 : G, (k y (M.op X0 X0)) = (M.op (k y y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6364 eq6444
    | exact resolve eq6444 eq6364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6444
  have eq6464 : (k y y) = (M.op (k y y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6364 eq6460
    | exact resolve eq6460 eq6364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6460
  have eq6467 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6451 eq6464
    | exact resolve eq6464 eq6451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6451 eq6464
  have eq6743 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq6467
       grind)
    | exact superpose eq6467 eq40
    | exact resolve eq40 eq6467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6467
  have eq6756 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6743
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6743
    | exact resolve eq6743 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6743
  have eq6775 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6756 eq1535
    | (have j0 := eq1535 (σ y) (σ y)
       grind)
    | (have r₁ := eq1535 (σ y) (σ y)
       have r₂ := eq6756
       grind)
    | exact resolve eq1535 eq6756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq6776 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6775
  have eq6777 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6776
  have eq6829 : x = (M.op (k y (σ y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6777 eq962
    | exact resolve eq962 eq6777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq6845 : y = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6777 eq6364
    | exact resolve eq6364 eq6777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6777
  have eq6849 : y = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6845
  have eq6873 : x = (M.op (k (σ y) (σ y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6849 eq6829
    | exact resolve eq6829 eq6849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6829
  have eq6905 : x = (M.op (σ y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6756 eq6873
    | exact resolve eq6873 eq6756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6756 eq6873
  have eq6964 : (M.op x y) = (M.op x (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6849
       grind)
    | exact superpose eq6849 eq18
    | exact resolve eq18 eq6849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6849
  have eq7434 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op (M.op X1 X1) x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6905 eq178
    | exact resolve eq178 eq6905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6905
  have eq7443 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (k x (M.op X1 X1)) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq7434 X0 X1
       have i₂ := eq929 x X1
       grind)
    | exact superpose eq929 eq7434
    | exact resolve eq7434 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7434
  have eq7448 : ∀ X0 X1 : G, (k (M.op x y) (M.op X0 X0)) = (M.op (k x (M.op X1 X1)) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq7443 X1 X1
       have i₂ := eq929 sF0 X1
       grind)
    | exact superpose eq929 eq7443
    | exact resolve eq7443 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7443
  have eq7452 : ∀ X0 : G, (k (M.op x y) (M.op X0 X0)) = (M.op (k x y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6364 eq7448
    | exact resolve eq7448 eq6364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7448
  have eq7454 : ∀ X0 : G, (k (M.op x y) (M.op X0 X0)) = (M.op x (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6322 eq7452
    | exact resolve eq7452 eq6322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6322 eq7452
  have eq7456 : (k (M.op x y) y) = (M.op x (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6364 eq7454
    | exact resolve eq7454 eq6364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6364 eq7454
  have eq7458 : x = (M.op x (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6459 eq7456
    | exact resolve eq7456 eq6459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6459 eq7456
  have eq7460 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6964 eq7458
    | exact resolve eq7458 eq6964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6964 eq7458
  have eq7461 : x = (M.op x y) := by grind
  clear eq7460
  have eq7464 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq7461
       grind)
    | exact superpose eq7461 eq22
    | exact resolve eq22 eq7461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq7468 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq1441
       have i₂ := eq7461
       grind)
    | exact superpose eq7461 eq1441
    | (have r₁ := eq1441
       have r₂ := eq7461
       grind)
    | exact resolve eq1441 eq7461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq7470 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op y y) := by grind
  clear eq7468
  have eq7474 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7464 eq20
    | exact resolve eq20 eq7464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7464
  have eq8923 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7470 eq40
    | exact resolve eq40 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7470
  have eq8931 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq8923
    | exact resolve eq8923 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8923
  have eq8934 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7474 eq8931
    | exact resolve eq8931 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8931
  have eq8943 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8934 eq1475
    | exact resolve eq1475 eq8934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8934
  have eq8952 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq8943
  have eq12712 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq8952 eq538
    | exact resolve eq538 eq8952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8952
  have eq12987 : ∀ X0 : G, (σ y) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq929 (M.op X0 X0) X0
       have i₂ := eq12712 (M.op X0 X0)
       grind)
    | exact superpose eq12712 eq929
    | exact resolve eq929 eq12712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13013 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq12712 eq12987
    | exact resolve eq12987 eq12712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12712 eq12987
  have eq13517 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq13013 eq152
    | exact resolve eq152 eq13013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq13013
  have eq13530 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq13517
    | exact resolve eq13517 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq13517
  have eq13533 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1537 y
       grind)
    | (have r₁ := eq13530
       have r₂ := eq1537 y
       grind)
    | exact resolve eq13530 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq13530
  have eq13566 : x = (M.op (M.op y y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq176 y
       have i₂ := eq13533
       grind)
    | exact superpose eq13533 eq176
    | exact resolve eq176 eq13533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq13573 : ∀ X0 : G, y = (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq538 y X0
       have i₂ := eq13533
       grind)
    | exact superpose eq13533 eq538
    | exact resolve eq538 eq13533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq13578 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq563 y X0 X1
       have i₂ := eq13533
       grind)
    | exact superpose eq13533 eq563
    | exact resolve eq563 eq13533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq13625 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (M.op X1 X1) y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 y X1 y X0
       have i₂ := eq13533
       grind)
    | exact superpose eq13533 eq178
    | exact resolve eq178 eq13533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13643 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op (k y (M.op X1 X1)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13625 X0 X1
       have i₂ := eq929 y X1
       grind)
    | exact superpose eq929 eq13625
    | exact resolve eq13625 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13625
  have eq13661 : ∀ X0 X1 : G, (M.op (k X1 (M.op X0 X0)) y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13578 X0 X1
       have i₂ := eq929 X1 X0
       grind)
    | exact superpose eq929 eq13578
    | exact resolve eq13578 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13578
  have eq13669 : x = (k (M.op x y) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13566
       have i₂ := eq929 sF0 y
       grind)
    | exact superpose eq929 eq13566
    | exact resolve eq13566 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13566
  have eq13672 : ∀ X0 X1 : G, (k y (M.op X0 X0)) = (M.op (k y (M.op X1 X1)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13643 X0 X1
       have i₂ := eq929 y X0
       grind)
    | exact superpose eq929 eq13643
    | exact resolve eq13643 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13643
  have eq13679 : ∀ X1 : G, (M.op (k X1 y) y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq13573 eq13661
    | exact resolve eq13661 eq13573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13661
  have eq13686 : (M.op x y) = (k (M.op x y) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13669
       have i₂ := eq7461
       grind)
    | exact superpose eq7461 eq13669
    | exact resolve eq13669 eq7461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7461 eq13669
  have eq13688 : ∀ X0 : G, (k y (M.op X0 X0)) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13573 eq13672
    | exact resolve eq13672 eq13573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13672
  have eq13692 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13533 eq13686
    | exact resolve eq13686 eq13533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13533 eq13686
  have eq13694 : (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13573 eq13688
    | exact resolve eq13688 eq13573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13688
  have eq13696 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13679 eq13694
    | exact resolve eq13694 eq13679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13679 eq13694
  have eq14021 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13692 eq40
    | exact resolve eq40 eq13692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13692
  have eq14029 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14021
    | exact resolve eq14021 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14021
  have eq14032 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7474 eq14029
    | exact resolve eq14029 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14029
  have eq14096 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq13696
       grind)
    | exact superpose eq13696 eq40
    | exact resolve eq40 eq13696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq13696
  have eq14113 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14096
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14096
    | exact resolve eq14096 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14096
  have eq14118 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14032 eq1475
    | exact resolve eq1475 eq14032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq14130 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14118
  have eq14197 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14130 eq177
    | exact resolve eq177 eq14130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq14225 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14130 eq963
    | exact resolve eq963 eq14130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq14254 : y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14130 eq13573
    | exact resolve eq13573 eq14130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14130
  have eq14260 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq14254
  have eq14290 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14113 eq14225
    | exact resolve eq14225 eq14113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14113 eq14225
  have eq14312 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14197
       have i₂ := eq929 sF4 sF3
       grind)
    | exact superpose eq929 eq14197
    | exact resolve eq14197 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14197
  have eq14347 : (σ x) = (k (M.op (σ x) (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13573 eq14312
    | exact resolve eq14312 eq13573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14312
  have eq14370 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14260 eq14347
    | exact resolve eq14347 eq14260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14347
  have eq14392 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq14260 eq27
    | exact resolve eq27 eq14260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14260
  have eq14402 : y = (σ y) := by
    first
    | (have r₁ := eq14392
       have r₂ := eq7474
       grind)
    | exact resolve eq14392 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14392
  have eq15007 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X1 X1) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq14290 eq178
    | exact resolve eq178 eq14290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq14290
  have eq15016 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ y))) = (M.op (k (σ x) (M.op X1 X1)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq15007 X0 X1
       have i₂ := eq929 sF2 X1
       grind)
    | exact superpose eq929 eq15007
    | exact resolve eq15007 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15007
  have eq15023 : ∀ X0 X1 : G, (k (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (k (σ x) (M.op X1 X1)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq15016 X1 X1
       have i₂ := eq929 sF4 X1
       grind)
    | exact superpose eq929 eq15016
    | exact resolve eq15016 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq15016
  have eq15030 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (k (σ x) y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13573 eq15023
    | exact resolve eq15023 eq13573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15023
  have eq15034 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15030 X0
       have i₂ := eq14402
       grind)
    | exact superpose eq14402 eq15030
    | exact resolve eq15030 eq14402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15030
  have eq15037 : (k (M.op (σ x) (σ y)) y) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13573 eq15034
    | exact resolve eq15034 eq13573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13573 eq15034
  have eq15039 : (k (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15037
       have i₂ := eq14402
       grind)
    | exact superpose eq14402 eq15037
    | exact resolve eq15037 eq14402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14402 eq15037
  have eq15041 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14032 eq15039
    | exact resolve eq15039 eq14032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14032 eq15039
  have eq15043 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15041
    | exact resolve eq15041 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15041
  have eq15045 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14370 eq15043
    | exact resolve eq15043 eq14370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14370 eq15043
  have eq15046 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15045
  have eq15048 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq15046 eq27
    | exact resolve eq27 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15046
  have eq15058 : False := by grind
  exact eq15058

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq36
  have eq74 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq108 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq108 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq117 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq49
    | exact resolve eq49 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq118 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq117
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq117
    | exact resolve eq117 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq136 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq141 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq109 sF1
       grind)
    | exact superpose eq109 eq138
    | exact resolve eq138 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq144 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq109 sF0
       grind)
    | exact superpose eq109 eq141
    | exact resolve eq141 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq141
  have eq433 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq51 X2 X3 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq51 X2 X3 X0
       grind)
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq54
  have eq593 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq433 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq433 (M.op X0 X0) X1
       grind)
    | exact superpose eq433 eq64
    | (have r₁ := eq64 X1 (M.op X1 X1) X2
       have r₂ := eq433 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq64 X0 (M.op X0 X0) X2
       have r₂ := eq433 X0 (M.op X0 X0)
       grind)
    | exact resolve eq64 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq594 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq593 X0 x X2
       grind)
    | (have r₁ := eq593 X0 x X2
       have r₂ := eq433 X0 x
       grind)
    | (have r₁ := eq593 x X0 X2
       have r₂ := eq433 X0 x
       grind)
    | exact resolve eq593 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq751 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq74 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq74 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq773 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq751 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq774 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq773 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq777 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq774
    | (have j0 := eq774 X0 X1
       grind)
    | exact resolve eq774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq5752 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq436 X1 x X2 x
       have i₂ := eq515 X1 x X2 x X0
       grind)
    | exact superpose eq515 eq436
    | exact resolve eq436 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq6262 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5752 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq436 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq436 eq5752
    | exact resolve eq5752 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq5752
  have eq7096 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6262 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6262
    | (have j0 := eq6262 x X0 y
       grind)
    | exact resolve eq6262 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6262
  have eq15617 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq777 X0 X1
       have j1 := eq770 X0 X1
       grind)
    | (have r₁ := eq777 X0 X1
       have r₂ := eq770 X0 X1
       grind)
    | (have r₁ := eq777 X1 X1
       have r₂ := eq770 X1 X1
       grind)
    | exact resolve eq777 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq777
  have eq15697 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15617 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15617
    | exact resolve eq15617 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15771 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15617 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15617
    | (have j0 := eq15617 x X0
       grind)
    | exact resolve eq15617 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15617
  have eq16134 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15697 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq15697
    | (have j0 := eq15697 X0 X1
       grind)
    | exact resolve eq15697 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq15697
  have eq33891 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15771 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15771
    | (have j0 := eq15771 y
       grind)
    | exact resolve eq15771 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771
  have eq33912 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33891
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq33891
    | exact resolve eq33891 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33891
  have eq33944 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq33912
    | exact resolve eq33912 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33912
  have eq34623 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16134 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq16134
    | (have j0 := eq16134 X1 X1
       grind)
    | exact resolve eq16134 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16134
  have eq35129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq34623 y x
       grind)
    | exact superpose eq34623 eq71
    | (have j1 := eq34623 x x
       grind)
    | exact resolve eq71 eq34623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq34623
  have eq35373 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35129
    | exact resolve eq35129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35129
  have eq35424 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq35373
    | exact resolve eq35373 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq35373
  have eq35456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq35424 eq33944
    | exact resolve eq33944 eq35424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33944 eq35424
  have eq35463 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq35456
       have r₂ := eq27
       grind)
    | exact resolve eq35456 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35456
  have eq35645 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq35463 eq118
    | exact resolve eq118 eq35463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq35463
  have eq35840 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq35645
    | exact resolve eq35645 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq35645
  have eq35841 : x = (M.op x x) := by grind
  clear eq35840
  have eq35847 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq35841
       have i₂ := eq433 X0 x
       grind)
    | (have i₁ := eq35841
       have i₂ := eq433 x X0
       grind)
    | exact superpose eq433 eq35841
    | exact resolve eq35841 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq35921 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq594 x x
       have i₂ := eq35841
       grind)
    | exact superpose eq35841 eq594
    | exact resolve eq594 eq35841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq35956 : y = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq7096 x
       have i₂ := eq35841
       grind)
    | exact superpose eq35841 eq7096
    | exact resolve eq7096 eq35841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7096
  have eq36016 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq35956
       have i₂ := eq35841
       grind)
    | exact superpose eq35841 eq35956
    | exact resolve eq35956 eq35841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35956
  have eq36377 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq35847 sF0
       grind)
    | exact superpose eq35847 eq144
    | exact resolve eq144 eq35847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq36463 : x = (σ x) := by
    first
    | (have i₁ := eq36377
       have i₂ := eq35847 sF1
       grind)
    | exact superpose eq35847 eq36377
    | exact resolve eq36377 eq35847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36377
  have eq36708 : x = (σ x) := by
    first
    | (have i₁ := eq36463
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36463
    | exact resolve eq36463 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq36463
  have eq36887 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq36708 eq26
    | exact resolve eq26 eq36708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq39749 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq136
       have i₂ := eq35921 sF0
       grind)
    | exact superpose eq35921 eq136
    | exact resolve eq136 eq35921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq39819 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) x) := by
    first
    | exact superpose eq36708 eq39749
    | exact resolve eq39749 eq36708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36708 eq39749
  have eq39891 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) x) := by
    first
    | (have i₁ := eq39819
       have i₂ := eq35921 sF1
       grind)
    | exact superpose eq35921 eq39819
    | exact resolve eq39819 eq35921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35921 eq39819
  have eq39950 : (σ y) = (M.op (σ (M.op x y)) x) := by
    first
    | exact superpose eq36016 eq39891
    | exact resolve eq39891 eq36016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36016 eq39891
  have eq39972 : (σ y) = (M.op (σ (M.op x y)) x) := by
    first
    | (have i₁ := eq39950
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39950
    | exact resolve eq39950 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq39950
  have eq40006 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) x) (σ y)) := by
    intro X0
    first
    | exact superpose eq39972 eq14
    | exact resolve eq14 eq39972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39972
  have eq40029 : (σ (M.op x y)) = (M.op (M.op x x) (σ y)) := by
    first
    | (have i₁ := eq40006 x
       have i₂ := eq35847 x
       grind)
    | exact superpose eq35847 eq40006
    | exact resolve eq40006 eq35847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35847 eq40006
  have eq40041 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq40029
       have i₂ := eq35841
       grind)
    | exact superpose eq35841 eq40029
    | exact resolve eq40029 eq35841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35841 eq40029
  have eq40051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36887 eq40041
    | exact resolve eq40041 eq36887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36887 eq40041
  have eq40057 : False := by grind
  exact eq40057

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq537 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq54 X2 X3 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq54 X2 X3 X0
       grind)
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq57
  have eq8241 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq537 X1 x X2 x
       have i₂ := eq641 X1 x X2 x X0
       grind)
    | exact superpose eq641 eq537
    | exact resolve eq537 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq8911 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8241 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq537 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq537 eq8241
    | exact resolve eq8241 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq8241
  have eq9982 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8911 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8911
    | (have j0 := eq8911 x X0 y
       grind)
    | exact resolve eq8911 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9983 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq27 eq8911
    | (have j0 := eq8911 (σ x) X0 (σ y)
       grind)
    | exact resolve eq8911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq29701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq29700
    | exact resolve eq29700 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29700
  have eq29711 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq29701
       have r₂ := eq28
       grind)
    | exact resolve eq29701 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29701
  have eq29714 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq29711
    | exact resolve eq29711 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29711
  have eq29859 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29714 eq8911
    | exact resolve eq8911 eq29714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29714
  have eq29862 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9983 eq29859
    | exact resolve eq29859 eq9983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9983 eq29859
  have eq29863 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29862
  have eq30008 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op X0 X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8911 x X0 x
       have i₂ := eq29863
       grind)
    | exact superpose eq29863 eq8911
    | exact resolve eq8911 eq29863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8911 eq29863
  have eq30011 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9982 eq30008
    | exact resolve eq30008 eq9982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9982 eq30008
  have eq30012 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq30011
  have eq30066 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq30012 eq30
    | exact resolve eq30 eq30012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq30012
  have eq30164 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq30066
    | exact resolve eq30066 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq30066
  have eq30165 : x = y := by grind
  clear eq30164
  have eq30329 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq30165
       grind)
    | exact superpose eq30165 eq19
    | exact resolve eq19 eq30165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq30330 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq30165
       grind)
    | exact superpose eq30165 eq25
    | exact resolve eq25 eq30165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq30165
  have eq30437 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq30330
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30330
    | exact resolve eq30330 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq30330
  have eq30452 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq30437 eq27
    | exact resolve eq27 eq30437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30437
  have eq30821 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq30452 eq69
    | exact resolve eq69 eq30452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq30452
  have eq30993 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq30821
       have i₂ := eq30329
       grind)
    | exact superpose eq30329 eq30821
    | exact resolve eq30821 eq30329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30329 eq30821
  have eq31006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30993 eq15
    | exact resolve eq15 eq30993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30993
  have eq31051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq31006
    | exact resolve eq31006 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31006
  have eq31060 : False := by grind
  exact eq31060

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq55 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq661 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X4 x X2
       have i₂ := eq57 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq57 X2 X2 X2 x
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x
       have i₂ := eq57 X1 X0 y x
       grind)
    | (have i₁ := eq55 (M.op y y)
       have i₂ := eq57 y y y x
       grind)
    | exact superpose eq57 eq55
    | exact resolve eq55 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq664 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x
       have i₂ := eq57 X0 X1 sF3 x
       grind)
    | (have i₁ := eq56 (M.op sF3 sF3)
       have i₂ := eq57 sF3 sF3 sF3 x
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq32107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq32108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq32107
    | exact resolve eq32107 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32107
  have eq32118 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq32108
       have r₂ := eq28
       grind)
    | exact resolve eq32108 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32108
  have eq32121 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq32118
    | exact resolve eq32118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32118
  have eq32278 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq32121 eq661
    | exact resolve eq661 eq32121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32121
  have eq32284 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq664 eq32278
    | exact resolve eq32278 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq32278
  have eq32285 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq32284
  have eq32449 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq661 X0 X1 y y
       have i₂ := eq32285
       grind)
    | exact superpose eq32285 eq661
    | exact resolve eq661 eq32285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq32285
  have eq32455 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq663 eq32449
    | exact resolve eq32449 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq32449
  have eq32456 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq32455
  have eq32525 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq32456 eq30
    | exact resolve eq30 eq32456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32456
  have eq32627 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq32525
    | exact resolve eq32525 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32525
  have eq32628 : x = y := by grind
  clear eq32627
  have eq32791 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32628
       grind)
    | exact superpose eq32628 eq19
    | exact resolve eq19 eq32628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32792 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq32628
       grind)
    | exact superpose eq32628 eq25
    | exact resolve eq25 eq32628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32628
  have eq32898 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq32792
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32792
    | exact resolve eq32792 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq32792
  have eq32913 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32898 eq27
    | exact resolve eq27 eq32898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32898
  have eq33317 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32913 eq69
    | exact resolve eq69 eq32913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq32913
  have eq33510 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq33317
       have i₂ := eq32791
       grind)
    | exact superpose eq32791 eq33317
    | exact resolve eq33317 eq32791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32791 eq33317
  have eq33524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33510 eq15
    | exact resolve eq15 eq33510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33510
  have eq33569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq33524
    | exact resolve eq33524 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq33524
  have eq33578 : False := by grind
  exact eq33578

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then Y else if m(X,Y) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_y_x_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq34 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq203 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq203 eq203
    | exact resolve eq203 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq558 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq558 X2 X0
       grind)
    | exact superpose eq558 eq16
    | exact resolve eq16 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq203 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq558 X2 (M.op X1 (M.op X0 X0))
       grind)
    | (have i₁ := eq203 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq558 (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact superpose eq558 eq203
    | exact resolve eq203 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq558 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq558 (M.op X1 X1) X0
       grind)
    | exact superpose eq558 eq16
    | exact resolve eq16 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq203 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq583 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq583 eq203
    | exact resolve eq203 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1256 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) ∨ (M.op (k X0 (M.op X1 X1)) (M.op X2 X0)) = X2 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq11 X0 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 (M.op X1 X1)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1257 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op (M.op X2 X2) X1)) = X0 ∨ (M.op (M.op (M.op X2 X2) X1) (M.op (M.op X2 X2) X1)) = (M.op (M.op X0 X1) (M.op (M.op X2 X2) X1)) ∨ (M.op X0 X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq11 (M.op X0 X1) (M.op (M.op X2 X2) X1)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op X0 X1) (M.op (M.op X2 X2) X1)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1277 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1278 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1287 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 X1) (M.op (M.op X2 X2) X1)) ∨ (k (M.op X0 X1) (M.op (M.op X2 X2) X1)) = X0 ∨ (M.op X0 X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1257 X0 X1 X2
       have i₂ := eq16 (M.op X2 X2) X2 X1
       grind)
    | exact superpose eq16 eq1257
    | (have j0 := eq1257 X0 X1 X2
       grind)
    | exact resolve eq1257 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq2578 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) x) (M.op x x)) ∨ (M.op x y) = (k y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq1277
       grind)
    | exact superpose eq1277 eq16
    | exact resolve eq16 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq2583 : x = y ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq2578 x
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq2578
    | exact resolve eq2578 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq2584 : (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq2583
  have eq2591 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1278 eq16
    | exact resolve eq16 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq2596 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2591 x
       have i₂ := eq16 sF2 x sF2
       grind)
    | exact superpose eq16 eq2591
    | exact resolve eq2591 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591
  have eq2597 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq2596
  have eq2601 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2584
       grind)
    | exact superpose eq2584 eq40
    | exact resolve eq40 eq2584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2584
  have eq2602 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2601
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2601
    | exact resolve eq2601 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601
  have eq2604 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq2602
    | exact resolve eq2602 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602
  have eq2612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2604 eq2597
    | exact resolve eq2597 eq2604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597 eq2604
  have eq2619 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2612
       have r₂ := eq27
       grind)
    | exact resolve eq2612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2612
  have eq2624 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2619 eq31
    | exact resolve eq31 eq2619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2619
  have eq2685 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq2624
    | exact resolve eq2624 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2624
  have eq2686 : x = y := by grind
  clear eq2685
  have eq2689 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2686
       grind)
    | exact superpose eq2686 eq18
    | exact resolve eq18 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2690 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2686
       grind)
    | exact superpose eq2686 eq24
    | exact resolve eq24 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2686
  have eq2698 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2690
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2690
    | exact resolve eq2690 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2690
  have eq2699 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2698 eq26
    | exact resolve eq26 eq2698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2698
  have eq2765 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 x X0
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq16
    | exact resolve eq16 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2766 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 x X1
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq203
    | exact resolve eq203 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq2769 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x y) (M.op X2 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 X2 x X1 X0
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq206
    | exact resolve eq206 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2773 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq558 x X0
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq558
    | exact resolve eq558 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2779 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq585 X1 X0 x
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq585
    | exact resolve eq585 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq2780 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 x X1
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq587
    | exact resolve eq587 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2781 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq587 x X1 X0
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq587
    | exact resolve eq587 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq2783 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X1 X0 x
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq665
    | exact resolve eq665 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq2689
  have eq2792 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq2780 x X1
       have i₂ := eq2783 x (M.op X1 sF0)
       grind)
    | exact superpose eq2783 eq2780
    | exact resolve eq2780 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2780
  have eq2799 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) (M.op X2 X1)) X2) = (M.op (M.op x y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq2769 x X1 X2
       have i₂ := eq2783 x X1
       grind)
    | exact superpose eq2783 eq2769
    | exact resolve eq2769 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769
  have eq2807 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq2699 eq16
    | exact resolve eq16 eq2699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2815 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq2699 eq558
    | exact resolve eq558 eq2699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq2699
  have eq2844 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2815 x
       have i₂ := eq2773 x
       grind)
    | exact superpose eq2773 eq2815
    | exact resolve eq2815 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815
  have eq2869 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq2844 eq27
    | exact resolve eq27 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2844
  have eq4039 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op x y)))) = (M.op (M.op (M.op X3 X3) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2766 eq206
    | exact resolve eq206 eq2766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq4064 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op x y)))) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4039 X0 X1 X2 x
       have i₂ := eq2783 x X0
       grind)
    | exact superpose eq2783 eq4039
    | exact resolve eq4039 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4039
  have eq4097 : ∀ X0 X2 : G, (M.op (M.op x y) (M.op X0 (M.op X2 (M.op x y)))) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq4064 X0 X0 X2
       have i₂ := eq2783 X0 (M.op X0 (M.op X2 sF0))
       grind)
    | exact superpose eq2783 eq4064
    | exact resolve eq4064 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4064
  have eq9057 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X1 ∨ (M.op (k X1 (M.op X0 X0)) (M.op X2 X1)) = X2 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2807 (M.op X0 X0) X1
       have i₂ := eq1256 X1 X0 X2
       grind)
    | (have i₁ := eq2807 (M.op X1 X1) (M.op X1 X1)
       have i₂ := eq1256 X0 X1 X2
       grind)
    | exact superpose eq1256 eq2807
    | (have j1 := eq1256 X1 X0 X2
       grind)
    | exact resolve eq2807 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq9117 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op (k X1 (M.op X0 X0)) (M.op X2 X1)) = X2 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq2807 eq9057
    | (have j0 := eq9057 X0 X1 X2
       grind)
    | exact resolve eq9057 eq2807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2807 eq9057
  have eq9118 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op (k X1 (M.op X0 X0)) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq9117 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9117
  have eq9294 : ∀ X0 X1 X2 : G, (M.op x y) = X1 ∨ (M.op (k X1 (M.op X0 X0)) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9118 X0 X1 X2
       have i₂ := eq2773 X0
       grind)
    | exact superpose eq2773 eq9118
    | (have j0 := eq9118 X0 X1 X2
       grind)
    | exact resolve eq9118 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9118
  have eq9453 : ∀ X1 X2 : G, (M.op (k X1 (M.op x y)) (M.op X2 X1)) = X2 ∨ (M.op x y) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq9294 x X1 X2
       have i₂ := eq2773 x
       grind)
    | exact superpose eq2773 eq9294
    | (have j0 := eq9294 x X1 X2
       grind)
    | exact resolve eq9294 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9294
  have eq10804 : ∀ X0 : G, (M.op (k X0 (M.op x y)) (M.op x y)) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq9453 eq2779
    | (have j1 := eq9453 X0 x
       grind)
    | exact resolve eq2779 eq9453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10805 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq9453 eq2781
    | (have j1 := eq9453 X0 x
       grind)
    | exact resolve eq2781 eq9453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781 eq9453
  have eq10966 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq10805 eq2792
    | (have j1 := eq10805 (M.op X0 (M.op x y))
       grind)
    | exact resolve eq2792 eq10805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11279 : ∀ X0 : G, (σ X0) = (k (σ (M.op X0 (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq10966 eq42
    | (have j1 := eq10966 X0
       grind)
    | exact resolve eq42 eq10966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10966
  have eq11388 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = (M.op (M.op (M.op (M.op x y) X0) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq4097 eq2799
    | exact resolve eq2799 eq4097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4097
  have eq11426 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11388 X0 X1
       have i₂ := eq2792 (M.op sF0 (M.op X1 sF0))
       grind)
    | exact superpose eq2792 eq11388
    | exact resolve eq11388 eq2792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11388
  have eq11520 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq2792 eq11426
    | exact resolve eq11426 eq2792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11524 : ∀ X0 X1 : G, (M.op (M.op (k X0 (M.op x y)) X1) X0) = X1 ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq10805 eq11426
    | (have j1 := eq10805 X0
       grind)
    | exact resolve eq11426 eq10805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11426
  have eq14770 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (k (M.op X1 X1) (M.op (M.op X0 X0) X1)) = X1 ∨ (M.op X1 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq583 X2 X1 (M.op (M.op X0 X0) X1)
       have i₂ := eq1287 X1 X1 X0
       grind)
    | exact superpose eq1287 eq583
    | (have j1 := eq1287 X1 X1 X0
       grind)
    | exact resolve eq583 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq14795 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op (M.op x y) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) ∨ (k (M.op X2 X1) (M.op (M.op X0 X0) X1)) = X2 ∨ (M.op (M.op X0 X0) X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2765 (M.op (M.op X0 X0) X1) (M.op X2 X1)
       have i₂ := eq1287 X2 X1 X0
       grind)
    | exact superpose eq1287 eq2765
    | (have j1 := eq1287 X2 X1 X0
       grind)
    | exact resolve eq2765 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq2765
  have eq14816 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op x y) X1) ∨ (k (M.op X2 X1) (M.op (M.op X0 X0) X1)) = X2 ∨ (M.op (M.op X0 X0) X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq2799 eq14795
    | (have j0 := eq14795 X0 X1 X2
       grind)
    | exact resolve eq14795 eq2799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799 eq14795
  have eq14840 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x y) (M.op X2 X2)) ∨ (k (M.op X1 X1) (M.op (M.op X0 X0) X1)) = X1 ∨ (M.op X1 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14770 X0 X1 X2
       have i₂ := eq2783 X0 (M.op X2 X2)
       grind)
    | exact superpose eq2783 eq14770
    | (have j0 := eq14770 X0 X1 X2
       grind)
    | exact resolve eq14770 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14770
  have eq14994 : ∀ X0 X1 X2 : G, (k (M.op X2 X1) (M.op (M.op x y) X1)) = X2 ∨ (M.op X2 X1) = (M.op (M.op x y) X1) ∨ (M.op (M.op X0 X0) X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14816 X0 X1 X2
       have i₂ := eq2783 X0 X1
       grind)
    | exact superpose eq2783 eq14816
    | (have j0 := eq14816 X0 X1 X2
       grind)
    | exact resolve eq14816 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14816
  have eq15017 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x y) (M.op x y)) ∨ (k (M.op X1 X1) (M.op (M.op X0 X0) X1)) = X1 ∨ (M.op X1 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14840 X0 X1 X1
       have i₂ := eq2779 sF0 X1
       grind)
    | exact superpose eq2779 eq14840
    | (have j0 := eq14840 X0 X1 x
       grind)
    | exact resolve eq14840 eq2779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2779 eq14840
  have eq15165 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op (M.op x y) X1) ∨ (k (M.op X2 X1) (M.op (M.op x y) X1)) = X2 ∨ (M.op X2 X1) = (M.op (M.op x y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq14994 x X1 X2
       have i₂ := eq2783 x X1
       grind)
    | exact superpose eq2783 eq14994
    | (have j0 := eq14994 x X1 X2
       grind)
    | exact resolve eq14994 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14994
  have eq15166 : ∀ X1 X2 : G, (k (M.op X2 X1) (M.op (M.op x y) X1)) = X2 ∨ (M.op X2 X1) = (M.op (M.op x y) X1) := by
    intro X1 X2
    first
    | (have j0 := eq15165 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15165
  have eq15189 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X0) X1) ∨ (k (M.op X1 X1) (M.op (M.op X0 X0) X1)) = X1 ∨ (M.op X1 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15017 X0 X1
       have i₂ := eq2773 sF0
       grind)
    | exact superpose eq2773 eq15017
    | (have j0 := eq15017 X0 X1
       grind)
    | exact resolve eq15017 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15017
  have eq15353 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ (k (M.op X1 X1) (M.op (M.op X0 X0) X1)) = X1 ∨ (M.op X1 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15189 X0 X1
       have i₂ := eq2783 X0 X1
       grind)
    | exact superpose eq2783 eq15189
    | (have j0 := eq15189 X0 X1
       grind)
    | exact resolve eq15189 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15189
  have eq15505 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op (M.op x y) X1)) = X1 ∨ (M.op x y) = (M.op (M.op x y) X1) ∨ (M.op X1 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15353 X0 X1
       have i₂ := eq2783 X0 X1
       grind)
    | exact superpose eq2783 eq15353
    | (have j0 := eq15353 X0 X1
       grind)
    | exact resolve eq15353 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15353
  have eq15628 : ∀ X0 X1 : G, (k (M.op x y) (M.op (M.op x y) X1)) = X1 ∨ (M.op x y) = (M.op (M.op x y) X1) ∨ (M.op X1 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15505 X0 X1
       have i₂ := eq2773 X1
       grind)
    | exact superpose eq2773 eq15505
    | (have j0 := eq15505 X0 X1
       grind)
    | exact resolve eq15505 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15505
  have eq15738 : ∀ X1 : G, (M.op X1 X1) = (M.op (M.op x y) X1) ∨ (k (M.op x y) (M.op (M.op x y) X1)) = X1 ∨ (M.op x y) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have i₁ := eq15628 x X1
       have i₂ := eq2783 x X1
       grind)
    | exact superpose eq2783 eq15628
    | (have j0 := eq15628 x X1
       grind)
    | exact resolve eq15628 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783 eq15628
  have eq15836 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ (k (M.op x y) (M.op (M.op x y) X1)) = X1 ∨ (M.op x y) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have i₁ := eq15738 X1
       have i₂ := eq2773 X1
       grind)
    | exact superpose eq2773 eq15738
    | (have j0 := eq15738 X1
       grind)
    | exact resolve eq15738 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773 eq15738
  have eq15837 : ∀ X1 : G, (k (M.op x y) (M.op (M.op x y) X1)) = X1 ∨ (M.op x y) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have j0 := eq15836 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15836
  have eq16582 : ∀ X0 : G, (k (M.op x y) (k X0 (M.op x y))) = X0 ∨ (M.op x y) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq10805 eq15837
    | (have j1 := eq10805 (k X0 (M.op x y))
       grind)
    | exact resolve eq15837 eq10805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10805 eq15837
  have eq16607 : ∀ X0 : G, (k (M.op x y) (k X0 (M.op x y))) = X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq16582 X0
       have j1 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq16582 x
       have r₂ := eq13 (k (M.op x y) (k x (M.op x y))) x
       grind)
    | (have r₁ := eq16582 X0
       have r₂ := eq13 X0 (k (M.op x y) (k X0 (M.op x y)))
       grind)
    | (have r₁ := eq16582 X0
       have r₂ := eq13 (M.op x y) (k X0 (M.op x y))
       grind)
    | exact resolve eq16582 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16582
  have eq17052 : ∀ X0 : G, (σ X0) = (k (σ (M.op x y)) (σ (k X0 (M.op x y)))) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq16607 eq38
    | (have j1 := eq16607 X0
       grind)
    | exact resolve eq38 eq16607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16607
  have eq17061 : ∀ X0 : G, (σ X0) = (k (σ (M.op x y)) (k (σ X0) (σ (M.op x y)))) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq42 eq17052
    | (have j0 := eq17052 X0
       grind)
    | exact resolve eq17052 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17052
  have eq21008 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op X0 (M.op x y))) ∨ (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11279 eq17061
    | (have j0 := eq17061 (M.op X0 (M.op x y))
       have j1 := eq11279 X0
       grind)
    | exact resolve eq17061 eq11279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11279 eq17061
  have eq21020 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op X0 (M.op x y))) ∨ (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq21008 X0
       have j1 := eq13 (M.op X0 (M.op x y)) (M.op x y)
       grind)
    | (have r₁ := eq21008 X0
       have r₂ := eq13 (k (σ (M.op x y)) (σ X0)) (σ (M.op X0 (M.op x y)))
       grind)
    | (have r₁ := eq21008 X0
       have r₂ := eq13 (σ (M.op X0 (M.op x y))) (k (σ (M.op x y)) (σ X0))
       grind)
    | (have r₁ := eq21008 X0
       have r₂ := eq13 (M.op x y) (k (M.op X0 (M.op x y)) (M.op x y))
       grind)
    | exact resolve eq21008 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21008
  have eq28663 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op (M.op x y) (M.op X1 (M.op x y)))) ∨ (M.op (M.op x y) (M.op X1 (M.op x y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq11520 eq15166
    | exact resolve eq15166 eq11520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15166
  have eq28859 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op (M.op x y) (M.op X1 (M.op x y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28663 X0 X1
       have i₂ := eq2792 (M.op sF0 (M.op X1 sF0))
       grind)
    | exact superpose eq2792 eq28663
    | (have j0 := eq28663 X0 X1
       grind)
    | exact resolve eq28663 eq2792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28663
  have eq28950 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28859 X0 X1
       have i₂ := eq2792 (M.op sF0 (M.op X1 sF0))
       grind)
    | exact superpose eq2792 eq28859
    | (have j0 := eq28859 X0 X1
       grind)
    | exact resolve eq28859 eq2792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28859
  have eq29845 : ∀ X0 X1 : G, (M.op X0 (k (M.op X0 (M.op x y)) X1)) = X1 ∨ (M.op X0 (M.op x y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2766 X0 X1
       have i₂ := eq28950 (M.op X0 sF0) X1
       grind)
    | exact superpose eq28950 eq2766
    | (have j1 := eq28950 (M.op X0 (k (M.op X0 (M.op x y)) X1)) X1
       grind)
    | exact resolve eq2766 eq28950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766 eq28950
  have eq35065 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (k X1 (M.op x y)) (M.op x y)) X0) ∨ (M.op x y) = X1 ∨ (M.op (k X1 (M.op x y)) (M.op x y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq29845 eq11524
    | (have j0 := eq11524 X1 X1
       have j1 := eq29845 (k X1 (M.op x y)) X0
       grind)
    | exact resolve eq11524 eq29845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35125 : ∀ X0 X1 : G, (M.op (k X1 (M.op x y)) (M.op x y)) = X0 ∨ (M.op x y) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | exact superpose eq10804 eq35065
    | (have j0 := eq35065 X0 X1
       have j1 := eq10804 X1
       grind)
    | exact resolve eq35065 eq10804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35065
  have eq48971 : ∀ X0 : G, (τ (k (σ (M.op x y)) (σ X0))) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21020 eq15
    | (have j1 := eq21020 X0
       grind)
    | exact resolve eq15 eq21020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21020
  have eq49060 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq58 eq48971
    | (have j0 := eq48971 X0
       grind)
    | exact resolve eq48971 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq48971
  have eq49293 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq49060 eq29845
    | (have j0 := eq29845 X0 (M.op x y)
       have j1 := eq49060 X0
       grind)
    | exact resolve eq29845 eq49060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29845 eq49060
  have eq49330 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq49293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49293
  have eq49457 : ∀ X0 : G, (k (M.op x y) (k X0 (M.op x y))) = X0 ∨ (M.op x y) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq10804 eq49330
    | (have j1 := eq10804 X0
       grind)
    | exact resolve eq49330 eq10804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10804 eq49330
  have eq49694 : ∀ X0 : G, (k (M.op x y) (k X0 (M.op x y))) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have j0 := eq49457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49457
  have eq50099 : ∀ X0 : G, (σ X0) = (k (σ (M.op x y)) (σ (k X0 (M.op x y)))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq49694 eq38
    | (have j1 := eq49694 X0
       grind)
    | exact resolve eq38 eq49694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq49694
  have eq50146 : ∀ X0 : G, (σ X0) = (k (σ (M.op x y)) (k (σ X0) (σ (M.op x y)))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq42 eq50099
    | (have j0 := eq50099 X0
       grind)
    | exact resolve eq50099 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq50099
  have eq50366 : ∀ X0 : G, (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq50146 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq50146
    | (have j0 := eq50146 (τ X0)
       grind)
    | exact resolve eq50146 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50146
  have eq79970 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x y) ∨ (M.op x y) = X1 ∨ (M.op x y) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11524 X0 X1
       have i₂ := eq35125 (M.op (k X0 sF0) X1) X1
       grind)
    | (have i₁ := eq11524 X0 X1
       have i₂ := eq35125 (k X0 sF0) X1
       grind)
    | exact superpose eq35125 eq11524
    | (have j0 := eq11524 (M.op X0 X1) X1
       have j1 := eq35125 X0 X1
       grind)
    | exact resolve eq11524 eq35125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11524 eq35125
  have eq80055 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op x y) = X1 ∨ (M.op X0 X1) = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq79970 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79970
  have eq80840 : ∀ X0 X1 : G, (M.op x y) ≠ (k X1 X0) ∨ (M.op x y) = X1 ∨ (M.op X0 X1) = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq80055 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80055
  have eq81742 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (k X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq50366 eq80840
    | (have j0 := eq80840 (k X0 (σ (M.op x y))) (σ (M.op x y))
       have j1 := eq50366 X0
       grind)
    | (have r₁ := eq80840 (k (M.op x y) (σ (M.op x y))) (σ (M.op x y))
       have r₂ := eq50366 (M.op x y)
       grind)
    | exact resolve eq80840 eq50366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80840
  have eq81777 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (M.op (k X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq81742 X0
       grind)
    | (have r₁ := eq81742 X0
       have r₂ := eq2869
       grind)
    | exact resolve eq81742 eq2869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81742
  have eq81829 : (M.op x y) = (M.op (k (M.op x y) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | (have j0 := eq81777 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81777
  have eq81850 : (σ (M.op x y)) = (M.op (M.op x y) (M.op (k (M.op x y) (σ (M.op x y))) (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq81829 eq11520
    | exact resolve eq11520 eq81829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11520 eq81829
  have eq81869 : (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq81850
       have i₂ := eq2792 (M.op sF0 (M.op (k sF0 sF1) sF0))
       grind)
    | exact superpose eq2792 eq81850
    | exact resolve eq81850 eq2792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792 eq81850
  have eq81935 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq81869 eq50366
    | (have j0 := eq50366 (M.op x y)
       grind)
    | exact resolve eq50366 eq81869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50366 eq81869
  have eq81958 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by grind
  clear eq81935
  have eq81978 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq81958
       have i₂ := eq34 sF1
       grind)
    | exact superpose eq34 eq81958
    | exact resolve eq81958 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq81958
  have eq82014 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have r₁ := eq81978
       have r₂ := eq2869
       grind)
    | exact resolve eq81978 eq2869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81978
  have eq82026 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq82014 eq14
    | exact resolve eq14 eq82014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82014
  have eq82044 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq82026 eq20
    | exact resolve eq20 eq82026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq82026
  have eq82171 : False := by grind
  exact eq82171

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pxy_y_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq339 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq357 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq342 (σ X0)
       grind)
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq357
  have eq423 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X1
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq61
    | exact resolve eq61 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq430 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq430 X0 X1
       grind)
    | exact resolve eq428 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq430
  have eq796 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq431 X0 (σ X1)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 X0 (σ X1)
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq847 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq796 (τ X0) X1
       grind)
    | exact superpose eq796 eq17
    | (have j1 := eq796 (τ X0) X1
       grind)
    | exact resolve eq17 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq796
  have eq1312 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq847 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq847
    | exact resolve eq847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq1380 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1312 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1312
    | (have j0 := eq1312 X0 X1
       grind)
    | exact resolve eq1312 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1899 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq802 x y
       grind)
    | exact superpose eq802 eq16
    | (have j1 := eq802 x y
       grind)
    | exact resolve eq16 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1948 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq802 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq2116 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1899
       have i₂ := eq1380 x y
       grind)
    | exact superpose eq1380 eq1899
    | (have j1 := eq1380 (σ x) (σ y)
       grind)
    | (have r₁ := eq1899
       have r₂ := eq1380 x y
       grind)
    | exact resolve eq1899 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2117 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2116
  have eq2158 : y ≠ y ∨ x = (M.op x x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2117
       grind)
    | exact superpose eq2117 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2117
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2117
       grind)
    | exact resolve eq13 eq2117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117
  have eq2169 : y = (k x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2158
  have eq69843 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1948 x y
       have i₂ := eq2169
       grind)
    | exact superpose eq2169 eq1948
    | (have j0 := eq1948 x y
       grind)
    | exact resolve eq1948 eq2169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948 eq2169
  have eq69853 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq69843
  have eq69854 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq69853
  have eq69864 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69854
       grind)
    | exact superpose eq69854 eq16
    | exact resolve eq16 eq69854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69883 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq69854
       grind)
    | exact superpose eq69854 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq69854
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq69854
       grind)
    | exact resolve eq13 eq69854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69854
  have eq69910 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq69883
  have eq69918 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69910
       have i₂ := eq376 x
       grind)
    | exact superpose eq376 eq69910
    | exact resolve eq69910 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq69910
  have eq69937 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69918
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq69918
    | exact resolve eq69918 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69918
  have eq135880 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1380 x y
       have i₂ := eq69937
       grind)
    | exact superpose eq69937 eq1380
    | (have j0 := eq1380 x y
       grind)
    | exact resolve eq1380 eq69937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380 eq69937
  have eq136110 : y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq135880
       have r₂ := eq69864
       grind)
    | exact resolve eq135880 eq69864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135880
  have eq136258 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69864
       have i₂ := eq136110
       grind)
    | exact superpose eq136110 eq69864
    | exact resolve eq69864 eq136110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69864 eq136110
  have eq136303 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq136258
  have eq136304 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq136303
  have eq136343 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq136304
       grind)
    | exact superpose eq136304 eq10
    | exact resolve eq10 eq136304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136304
  have eq136600 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq136343
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq136343
    | exact resolve eq136343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136343
  have eq136601 : x = (M.op x x) := by grind
  clear eq136600
  have eq136658 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq92 x x
       have i₂ := eq136601
       grind)
    | exact superpose eq136601 eq92
    | (have r₁ := eq92 x x
       have r₂ := eq136601
       grind)
    | exact resolve eq92 eq136601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq136770 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq136658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136658
  have eq136915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1899
       have i₂ := eq136770 y
       grind)
    | exact superpose eq136770 eq1899
    | exact resolve eq1899 eq136770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq136770
  have eq136964 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq136915
  have eq137009 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq136964
       grind)
    | exact superpose eq136964 eq16
    | exact resolve eq16 eq136964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137010 : (σ x) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq423 x (σ y)
       have i₂ := eq136964
       grind)
    | exact superpose eq136964 eq423
    | exact resolve eq423 eq136964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq137103 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq137010
       have i₂ := eq136601
       grind)
    | exact superpose eq136601 eq137010
    | exact resolve eq137010 eq136601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137010
  have eq137174 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq136964
       have i₂ := eq137103
       grind)
    | exact superpose eq137103 eq136964
    | exact resolve eq136964 eq137103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136964 eq137103
  have eq137472 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq137174
       grind)
    | exact superpose eq137174 eq10
    | exact resolve eq10 eq137174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137174
  have eq137729 : x = y := by
    first
    | (have i₁ := eq137472
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq137472
    | exact resolve eq137472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137472
  have eq138420 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq137009
       have i₂ := eq137729
       grind)
    | exact superpose eq137729 eq137009
    | exact resolve eq137009 eq137729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137009 eq137729
  have eq138424 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq138420
       have i₂ := eq136601
       grind)
    | exact superpose eq136601 eq138420
    | exact resolve eq138420 eq136601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136601 eq138420
  have eq138425 : False := by grind
  exact eq138425
