import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3737`: `x ◇ y = (x ◇ z) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_pxx_pyx_Equation3737 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3737 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3737.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X2) X3 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X2 (M.op X1 X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X0 X3) (M.op X1 X3)
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq56 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    grind
  have eq58 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X1 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq60 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    grind
  clear eq50
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq60
    | exact resolve eq60 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq17
    | exact resolve eq17 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X1 X2) X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq62
    | exact resolve eq62 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq62 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq62
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq62 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq154 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X1 X3)) X4) = (M.op (M.op X2 (M.op X0 X3)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X2 (M.op X0 X3) (M.op X1 X3) X4
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X1 X5))) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X4 (M.op X0 (M.op X5 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq23 X4 (M.op X0 (M.op X5 X2)) X3 (M.op X1 X5)
       have i₂ := eq23 X1 X5 X0 X2
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X1 X5))) = (M.op (M.op X3 (M.op (M.op X5 X2) (M.op X1 X2))) X4) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq193 x X1 X2 X3 X4 X5
       have i₂ := eq154 x (M.op X5 X2) X3 (M.op X1 X2) X4
       grind)
    | exact superpose eq154 eq193
    | exact resolve eq193 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq193
  have eq226 : ∀ X1 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X1 X5))) = (M.op (M.op X3 (M.op X5 X1)) X4) := by
    intro X1 X3 X4 X5
    first
    | (have i₁ := eq224 X1 x X3 X4 X5
       have i₂ := eq8 X5 X1 x
       grind)
    | exact superpose eq8 eq224
    | exact resolve eq224 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq282 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq75 X0 X1
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq75 (σ X0) X1
       grind)
    | exact superpose eq75 eq29
    | (have j1 := eq75 (σ X0) X1
       grind)
    | exact resolve eq29 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq75
  have eq297 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq306 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq382 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X1)) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq297 X0 X1
       grind)
    | exact superpose eq297 eq62
    | (have j1 := eq297 X0 X2
       grind)
    | exact resolve eq62 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 (M.op X0 (M.op X1 X1)))) = (M.op X2 (M.op X3 (k (M.op X1 X1) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X3 (M.op X0 (M.op X1 X1)) X2 (k (M.op X1 X1) X1)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq23
    | exact resolve eq23 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq56
  have eq624 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 (M.op X0 (M.op X1 X1)))) = (M.op X2 (M.op X3 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq613 X0 X1 X2 X3
       have i₂ := eq55 X1
       grind)
    | exact superpose eq55 eq613
    | exact resolve eq613 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq613
  have eq646 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op X3 (M.op X1 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq624 x X1 X2 X3
       have i₂ := eq8 X2 X3 (M.op x (M.op X1 X1))
       grind)
    | exact superpose eq8 eq624
    | exact resolve eq624 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq904 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))) ∨ (M.op X0 X1) = (k (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 (M.op x (M.op X1 X1)) X2
       have i₂ := eq646 X1 X2 x
       grind)
    | exact superpose eq646 eq124
    | exact resolve eq124 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq124 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq904 X0 X1 X2
       have i₂ := eq8 X1 X1 (M.op X2 X2)
       grind)
    | exact superpose eq8 eq904
    | (have j0 := eq904 X0 X1 X2
       grind)
    | (have r₁ := eq904 X0 X0 X2
       have r₂ := eq8 X0 X0 (M.op X2 X2)
       grind)
    | exact resolve eq904 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq956 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq38 x y
       grind)
    | exact superpose eq38 eq14
    | (have j1 := eq38 x y
       grind)
    | exact resolve eq14 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X1) X2 (σ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq8
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq8 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1074 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq906 (σ X0)
       grind)
    | exact superpose eq906 eq13
    | exact resolve eq13 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0 X0
       have i₂ := eq906 (τ X0)
       grind)
    | exact superpose eq906 eq41
    | exact resolve eq41 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1076 X0
       have i₂ := eq906 X0
       grind)
    | exact superpose eq906 eq1076
    | exact resolve eq1076 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1081 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1074 X0
       have i₂ := eq906 X0
       grind)
    | exact superpose eq906 eq1074
    | exact resolve eq1074 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1140 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op (τ X1) (τ X1))) X1) ∨ (M.op (M.op (τ X1) (τ X1)) X0) = (k X0 (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (M.op (τ X1) (τ X1))
       have i₂ := eq58 (τ X1) X0
       grind)
    | (have i₁ := eq17 X0 X1
       have i₂ := eq58 X0 (k X1 (τ X0))
       grind)
    | exact superpose eq58 eq17
    | (have j1 := eq58 (τ X1) X0
       grind)
    | exact resolve eq17 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1154 : ∀ X0 X1 : G, (σ X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op (M.op (τ X1) (τ X1)) X0) = (k X0 (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1140 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq1140
    | (have j0 := eq1140 X0 X1
       grind)
    | exact resolve eq1140 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1140
  have eq1172 : ∀ X0 X1 : G, (σ X0) = (σ (τ (M.op X1 X1))) ∨ (M.op (M.op (τ X1) (τ X1)) X0) = (k X0 (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1154 X0 X1
       have i₂ := eq1079 X1
       grind)
    | exact superpose eq1079 eq1154
    | (have j0 := eq1154 X0 X1
       grind)
    | exact resolve eq1154 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1180 : ∀ X0 X1 : G, (σ X0) = (M.op X1 X1) ∨ (M.op (M.op (τ X1) (τ X1)) X0) = (k X0 (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1172 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq1172
    | (have j0 := eq1172 X0 X1
       grind)
    | exact resolve eq1172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1188 : ∀ X0 X1 : G, (M.op (τ (M.op X1 X1)) X0) = (k X0 (τ (M.op X1 X1))) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1180 X0 X0
       have i₂ := eq1079 X0
       grind)
    | exact superpose eq1079 eq1180
    | (have j0 := eq1180 X0 X1
       grind)
    | exact resolve eq1180 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1230 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X2 (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq646 (τ X0) X1 X2
       have i₂ := eq1079 X0
       grind)
    | exact superpose eq1079 eq646
    | exact resolve eq646 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1336 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1 (σ X0)
       have i₂ := eq1081 X0
       grind)
    | exact superpose eq1081 eq8
    | exact resolve eq8 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1525 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 (τ (M.op X1 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2 (τ (M.op X1 X1))
       have i₂ := eq1230 X1 (M.op X0 (τ (M.op X1 X1))) X2
       grind)
    | exact superpose eq1230 eq8
    | exact resolve eq8 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq3338 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq3507 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3338 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3338
    | (have j0 := eq3338 X0 X1
       grind)
    | exact resolve eq3338 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq4168 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq297 X0 X0
       have i₂ := eq306 X0 X1
       grind)
    | exact superpose eq306 eq297
    | (have j0 := eq297 X0 X1
       have j1 := eq306 X0 X1
       grind)
    | exact resolve eq297 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq4182 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq306 X1 (σ X0)
       grind)
    | exact superpose eq306 eq13
    | (have j1 := eq306 X1 X1
       grind)
    | exact resolve eq13 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq4195 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168
  have eq4210 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4182 X0 X1
       have i₂ := eq906 X1
       grind)
    | exact superpose eq906 eq4182
    | (have j0 := eq4182 X0 X1
       grind)
    | exact resolve eq4182 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4182
  have eq6467 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq956
       have i₂ := eq3507 y x
       grind)
    | exact superpose eq3507 eq956
    | (have j1 := eq3507 (σ y) (σ x)
       grind)
    | (have r₁ := eq956
       have r₂ := eq3507 y x
       grind)
    | exact resolve eq956 eq3507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956 eq3507
  have eq6468 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq6467
  have eq6474 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6468
       have i₂ := eq1081 x
       grind)
    | exact superpose eq1081 eq6468
    | exact resolve eq6468 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6468
  have eq6968 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq6474
       grind)
    | exact superpose eq6474 eq9
    | exact resolve eq9 eq6474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6474
  have eq7004 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6968
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6968
    | exact resolve eq6968 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6968
  have eq7005 : y = (M.op x x) := by grind
  clear eq7004
  have eq7161 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq125 x x
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq125
    | exact resolve eq125 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq7164 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq646 x X0 X1
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq646
    | exact resolve eq646 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7178 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op X1 y)) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 x x X1
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq22
    | exact resolve eq22 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq7184 : y = (k y y) := by
    first
    | (have i₁ := eq62 x x
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq62
    | exact resolve eq62 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq7202 : y = (M.op y y) := by
    first
    | (have i₁ := eq7184
       have i₂ := eq906 y
       grind)
    | exact superpose eq906 eq7184
    | exact resolve eq7184 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq7184
  have eq9486 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X2 (M.op y X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq226 y X0 X2 X1
       have i₂ := eq7164 X0 X1
       grind)
    | exact superpose eq7164 eq226
    | exact resolve eq226 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9557 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 y
       have i₂ := eq7164 (M.op X0 y) X1
       grind)
    | exact superpose eq7164 eq8
    | exact resolve eq8 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11064 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X1 (M.op X0 y)
       have i₂ := eq9557 X0 X1
       grind)
    | exact superpose eq9557 eq124
    | (have j0 := eq124 X1 X0
       grind)
    | (have r₁ := eq124 X1 (M.op X1 y)
       have r₂ := eq9557 X1 X1
       grind)
    | (have r₁ := eq124 (M.op X0 y) X0
       have r₂ := eq9557 X0 (M.op X0 y)
       grind)
    | exact resolve eq124 eq9557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq11580 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ y = (k x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq7161 (M.op X0 y)
       have i₂ := eq9557 X0 x
       grind)
    | exact superpose eq9557 eq7161
    | (have j0 := eq7161 X0
       grind)
    | exact resolve eq7161 eq9557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11583 : ∀ X0 X1 : G, y ≠ (M.op X0 x) ∨ y = (k x (M.op X0 (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7161 (M.op X0 (τ (M.op X1 X1)))
       have i₂ := eq1525 X0 X1 x
       grind)
    | exact superpose eq1525 eq7161
    | (have j0 := eq7161 X0
       grind)
    | exact resolve eq7161 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq7161
  have eq20150 : ∀ X0 : G, (k X0 (τ y)) = (M.op (τ y) X0) ∨ (σ X0) = y := by
    intro X0
    first
    | (have i₁ := eq1188 X0 y
       have i₂ := eq7202
       grind)
    | exact superpose eq7202 eq1188
    | exact resolve eq1188 eq7202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq36107 : y ≠ y ∨ y = (k x (M.op x y)) := by
    first
    | (have i₁ := eq11580 x
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq11580
    | (have j0 := eq11580 x
       grind)
    | (have r₁ := eq11580 x
       have r₂ := eq7005
       grind)
    | exact resolve eq11580 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11580
  have eq36108 : y = (k x (M.op x y)) := by grind
  clear eq36107
  have eq36621 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq382 x y X0
       have i₂ := eq36108
       grind)
    | exact superpose eq36108 eq382
    | (have j0 := eq382 x x X0
       grind)
    | exact resolve eq382 eq36108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq37234 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op (τ X0) x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17 X0 x
       have i₂ := eq36621 (τ X0)
       grind)
    | exact superpose eq36621 eq17
    | exact resolve eq17 eq36621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq36621
  have eq42877 : ∀ X0 : G, (k X0 (σ (τ y))) = (σ (M.op (τ y) (τ X0))) ∨ (σ (τ X0)) = y := by
    intro X0
    first
    | (have i₁ := eq16 X0 (τ y)
       have i₂ := eq20150 (τ X0)
       grind)
    | exact superpose eq20150 eq16
    | (have j1 := eq20150 (τ X0)
       grind)
    | exact resolve eq16 eq20150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20150
  have eq42880 : ∀ X0 : G, (k X0 y) = (σ (M.op (τ y) (τ X0))) ∨ (σ (τ X0)) = y := by
    intro X0
    first
    | (have i₁ := eq42877 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq42877
    | (have j0 := eq42877 X0
       grind)
    | exact resolve eq42877 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42877
  have eq42895 : ∀ X0 : G, (k X0 y) = (σ (M.op (τ y) (τ X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq42880 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42880
    | (have j0 := eq42880 X0
       grind)
    | exact resolve eq42880 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42880
  have eq43583 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (σ (τ (k X0 X1))) (M.op X2 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq957 (τ X0) (τ X1) X2
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq957
    | (have j0 := eq957 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq957 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq957
  have eq44385 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (σ (τ (k X0 X1))) (M.op X2 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43583 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43583
    | (have j0 := eq43583 X0 X1 X2
       grind)
    | exact resolve eq43583 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43583
  have eq44601 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X2 X0)) = (M.op (σ (τ X1)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44385 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq44385
    | (have j0 := eq44385 X0 X1 X2
       grind)
    | exact resolve eq44385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44385
  have eq44703 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k X0 X1) (M.op X2 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44601 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq44601
    | (have j0 := eq44601 X0 X1 X2
       grind)
    | exact resolve eq44601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44601
  have eq44743 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X2) = (M.op (k X0 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44703 X0 X1 X2
       have i₂ := eq1081 (τ X1)
       grind)
    | exact superpose eq1081 eq44703
    | (have j0 := eq44703 X0 X1 X2
       grind)
    | exact resolve eq44703 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44703
  have eq44759 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X2) = (M.op (k X0 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44743 X0 X1 X2
       have i₂ := eq1079 X1
       grind)
    | exact superpose eq1079 eq44743
    | (have j0 := eq44743 X0 X1 X2
       grind)
    | exact resolve eq44743 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44743
  have eq44768 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X2) = (M.op (k X0 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44759 X0 X1 X2
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq44759
    | (have j0 := eq44759 X0 X1 X2
       grind)
    | exact resolve eq44759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44759
  have eq44771 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X2) = (M.op (k X0 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44768 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44768
    | (have j0 := eq44768 X0 X1 X2
       grind)
    | exact resolve eq44768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44768
  have eq65034 : ∀ X0 : G, (M.op (k X0 y) (k X0 y)) = (σ (M.op (M.op (τ y) (τ X0)) (M.op (τ y) (τ X0)))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq1081 (M.op (τ y) (τ X0))
       have i₂ := eq42895 X0
       grind)
    | exact superpose eq42895 eq1081
    | (have j1 := eq42895 X0
       grind)
    | exact resolve eq1081 eq42895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42895
  have eq65036 : ∀ X0 : G, (σ (M.op (τ y) (τ y))) = (M.op (k X0 y) (k X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq65034 X0
       have i₂ := eq8 (τ y) (τ y) (τ X0)
       grind)
    | exact superpose eq8 eq65034
    | (have j0 := eq65034 X0
       grind)
    | exact resolve eq65034 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65034
  have eq65058 : ∀ X0 : G, (σ (τ (M.op y y))) = (M.op (k X0 y) (k X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq65036 X0
       have i₂ := eq1079 y
       grind)
    | exact superpose eq1079 eq65036
    | (have j0 := eq65036 X0
       grind)
    | exact resolve eq65036 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65036
  have eq65067 : ∀ X0 : G, (M.op y y) = (M.op (k X0 y) (k X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq65058 X0
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq65058
    | (have j0 := eq65058 X0
       grind)
    | exact resolve eq65058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65058
  have eq65073 : ∀ X0 : G, y = (M.op (k X0 y) (k X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq65067 X0
       have i₂ := eq7202
       grind)
    | exact superpose eq7202 eq65067
    | (have j0 := eq65067 (M.op (k X0 y) (k X0 y))
       grind)
    | exact resolve eq65067 eq7202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65067
  have eq69926 : ∀ X0 : G, (σ (M.op X0 x)) = (k (σ x) (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq37234 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37234
    | exact resolve eq37234 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37234
  have eq70013 : ∀ X0 : G, (σ (M.op X0 x)) = (σ (k x X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq69926 X0
       have i₂ := eq13 x X0
       grind)
    | exact superpose eq13 eq69926
    | exact resolve eq69926 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69926
  have eq78221 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X1)) = X0 ∨ (k (σ X0) X2) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X0 X2
       have i₂ := eq4195 X0 X1
       grind)
    | exact superpose eq4195 eq70
    | (have j1 := eq4195 X0 X2
       grind)
    | exact resolve eq70 eq4195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq4195
  have eq121582 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1336 x X0
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq1336
    | exact resolve eq1336 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq125462 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op X0 (M.op (σ x) y)) := by
    intro X0
    first
    | (have i₁ := eq9486 X0 (σ x) (σ y)
       have i₂ := eq121582 y
       grind)
    | exact superpose eq121582 eq9486
    | exact resolve eq9486 eq121582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125640 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq125462 X0
       have i₂ := eq7164 X0 (σ x)
       grind)
    | exact superpose eq7164 eq125462
    | exact resolve eq125462 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125462
  have eq176166 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq913 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq176316 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op X0 y)) = (k (M.op X0 (M.op X1 X1)) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq176166 (M.op X0 y) X1
       have i₂ := eq9557 X0 (M.op X1 X1)
       grind)
    | exact superpose eq9557 eq176166
    | exact resolve eq176166 eq9557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9557 eq176166
  have eq176416 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 (M.op X1 X1)) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq176316 X0 X1
       have i₂ := eq8 X0 X0 y
       grind)
    | exact superpose eq8 eq176316
    | exact resolve eq176316 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176316
  have eq185240 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq176416 (M.op X0 X1) X1
       have i₂ := eq8 X0 X1 X1
       grind)
    | exact superpose eq8 eq176416
    | exact resolve eq176416 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176416
  have eq185280 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) (M.op (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq185240 X0 X1
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq185240
    | exact resolve eq185240 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185240
  have eq229177 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (k x X0)) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq125640 (σ X0)
       have i₂ := eq4210 X0 x
       grind)
    | exact superpose eq4210 eq125640
    | (have j1 := eq4210 X0 x
       grind)
    | exact resolve eq125640 eq4210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4210 eq125640
  have eq229281 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (k x X0)) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq229177 X0
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq229177
    | (have j0 := eq229177 X0
       grind)
    | exact resolve eq229177 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229177
  have eq238039 : ∀ X0 : G, y ≠ y ∨ y = (k x (M.op x (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11583 x X0
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq11583
    | (have j0 := eq11583 x X0
       grind)
    | (have r₁ := eq11583 x x
       have r₂ := eq7005
       grind)
    | exact resolve eq11583 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11583
  have eq238040 : ∀ X0 : G, y = (k x (M.op x (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq238039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238039
  have eq238210 : ∀ X0 : G, y = (k x (M.op x (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq238040 (σ X0)
       have i₂ := eq1081 X0
       grind)
    | exact superpose eq1081 eq238040
    | exact resolve eq238040 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238040
  have eq238490 : ∀ X0 : G, y = (k x (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq238210 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq238210
    | exact resolve eq238210 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238210
  have eq264441 : ∀ X0 : G, (σ (M.op X0 x)) = (M.op (σ (M.op X0 x)) (σ y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq229281 X0
       have i₂ := eq70013 X0
       grind)
    | exact superpose eq70013 eq229281
    | exact resolve eq229281 eq70013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70013 eq229281
  have eq264459 : ∀ X0 : G, (σ (M.op X0 x)) = (M.op (σ (M.op X0 x)) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq264441 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264441
  have eq284849 : ∀ X0 : G, (M.op X0 x) = (M.op (k x X0) y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq44771 x X0 x
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq44771
    | (have j0 := eq44771 x X0 x
       grind)
    | exact resolve eq44771 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284864 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (k X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq646 X1 X2 (k X1 X0)
       have i₂ := eq44771 X1 X0 X1
       grind)
    | exact superpose eq44771 eq646
    | (have j1 := eq44771 X1 X0 X2
       grind)
    | exact resolve eq646 eq44771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq44771
  have eq284916 : ∀ X0 : G, x = (k x (M.op x y)) ∨ (M.op X0 x) = (M.op (k x X0) y) := by
    intro X0
    first
    | (have i₁ := eq185280 X0 X0
       have i₂ := eq284849 X0
       grind)
    | exact superpose eq284849 eq185280
    | (have j1 := eq284849 X0
       grind)
    | exact resolve eq185280 eq284849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185280 eq284849
  have eq284924 : ∀ X0 : G, (M.op X0 x) = (M.op (k x X0) y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq284916 X0
       have i₂ := eq36108
       grind)
    | exact superpose eq36108 eq284916
    | (have j0 := eq284916 X0
       grind)
    | exact resolve eq284916 eq36108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284916
  have eq285018 : ∀ X0 X1 : G, (M.op (M.op X1 x) (k x X0)) = (M.op (M.op X1 x) (M.op X0 x)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq7178 X1 (k x X0)
       have i₂ := eq284924 X0
       grind)
    | exact superpose eq284924 eq7178
    | exact resolve eq7178 eq284924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7178 eq284924
  have eq285037 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 x) (k x X0)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq285018 X0 X1
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq285018
    | exact resolve eq285018 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285018
  have eq286509 : ∀ X0 : G, (M.op x X0) = (M.op y (k x X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq285037 X0 x
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq285037
    | exact resolve eq285037 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285037
  have eq292083 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq36108
       have i₂ := eq78221 x y X0
       grind)
    | exact superpose eq78221 eq36108
    | (have j1 := eq78221 x x X0
       grind)
    | exact resolve eq36108 eq78221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36108 eq78221
  have eq296001 : ∀ X0 : G, y = (M.op (k X0 y) (M.op y X0)) ∨ y = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq65073 X0
       have i₂ := eq284864 y X0 (k X0 y)
       grind)
    | exact superpose eq284864 eq65073
    | (have j0 := eq65073 (M.op (k X0 y) (M.op y X0))
       have j1 := eq284864 y X0 x
       grind)
    | exact resolve eq65073 eq284864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65073 eq284864
  have eq296033 : ∀ X0 : G, y = X0 ∨ y = (M.op (k X0 y) (M.op y X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq296001 X0
       have i₂ := eq7202
       grind)
    | exact superpose eq7202 eq296001
    | (have j0 := eq296001 X0
       grind)
    | exact resolve eq296001 eq7202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296001
  have eq296034 : ∀ X0 : G, y = (M.op (k X0 y) (M.op y X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq296033 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296033
  have eq296163 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) y) = (M.op X0 (k X1 y)) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (k X1 y) (M.op y X1)
       have i₂ := eq296034 X1
       grind)
    | exact superpose eq296034 eq8
    | (have j1 := eq296034 X1
       grind)
    | exact resolve eq8 eq296034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296034
  have eq296183 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X1 y))) = (M.op X0 (k X1 y)) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq296163 X0 X1
       have i₂ := eq226 X1 X0 y y
       grind)
    | exact superpose eq226 eq296163
    | (have j0 := eq296163 X0 X1
       grind)
    | exact resolve eq296163 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq296163
  have eq296236 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op X0 (k X1 y)) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq296183 X0 X1
       have i₂ := eq7164 y X1
       grind)
    | exact superpose eq7164 eq296183
    | (have j0 := eq296183 X0 X1
       grind)
    | exact resolve eq296183 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7164 eq296183
  have eq297166 : ∀ X0 : G, y = (k x (M.op x (M.op (k X0 y) (M.op y X0)))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq238490 (k X0 y)
       have i₂ := eq296236 (k X0 y) X0
       grind)
    | exact superpose eq296236 eq238490
    | (have j1 := eq296236 X0 (k x (M.op x (M.op (k X0 y) (M.op y X0))))
       grind)
    | exact resolve eq238490 eq296236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238490 eq296236
  have eq297411 : ∀ X0 : G, y = (k x (M.op (M.op x X0) (k X0 y))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq297166 X0
       have i₂ := eq9486 x X0 (k X0 y)
       grind)
    | exact superpose eq9486 eq297166
    | (have j0 := eq297166 (k x (M.op (M.op x X0) (k X0 y)))
       grind)
    | exact resolve eq297166 eq9486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297166
  have eq297982 : y = (k x (M.op y (k x y))) ∨ x = y := by
    first
    | (have i₁ := eq297411 x
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq297411
    | (have j0 := eq297411 (k x (M.op y (k x y)))
       grind)
    | exact resolve eq297411 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297411
  have eq298126 : (M.op y y) = (M.op x (M.op y (k x y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq286509 (M.op y (k x y))
       have i₂ := eq297982
       grind)
    | exact superpose eq297982 eq286509
    | exact resolve eq286509 eq297982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286509 eq297982
  have eq298155 : (M.op y y) = (M.op x (M.op y (k x y))) ∨ x = y := by grind
  clear eq298126
  have eq298184 : y = (M.op x (M.op y (k x y))) ∨ x = y := by
    first
    | (have i₁ := eq298155
       have i₂ := eq7202
       grind)
    | exact superpose eq7202 eq298155
    | exact resolve eq298155 eq7202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7202 eq298155
  have eq298576 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 (k x y)) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9486 X0 (k x y) x
       have i₂ := eq298184
       grind)
    | exact superpose eq298184 eq9486
    | exact resolve eq9486 eq298184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9486 eq298184
  have eq299104 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq264459 (M.op X0 (k x y))
       have i₂ := eq298576 X0
       grind)
    | exact superpose eq298576 eq264459
    | exact resolve eq264459 eq298576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264459 eq298576
  have eq299108 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq299104 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299104
  have eq319354 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 y)) := by
    intro X0
    first
    | (have j0 := eq11064 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11064
  have eq319637 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) y))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op (τ X0) y)
       have i₂ := eq319354 (τ X0)
       grind)
    | exact superpose eq319354 eq16
    | exact resolve eq16 eq319354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq319354
  have eq319775 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = (k X0 (σ (M.op (τ X0) y))) := by
    intro X0
    first
    | (have i₁ := eq319637 X0
       have i₂ := eq1079 X0
       grind)
    | exact superpose eq1079 eq319637
    | exact resolve eq319637 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq319637
  have eq319823 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (τ X0) y))) := by
    intro X0
    first
    | (have i₁ := eq319775 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq319775
    | exact resolve eq319775 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319775
  have eq319938 : (M.op (σ x) (σ x)) = (M.op (σ (M.op (τ (σ x)) y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq292083 (σ (M.op (τ (σ x)) y))
       have i₂ := eq319823 (σ x)
       grind)
    | exact superpose eq319823 eq292083
    | exact resolve eq292083 eq319823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292083 eq319823
  have eq320070 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq319938
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq319938
    | exact resolve eq319938 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319938
  have eq320126 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq320070
       have i₂ := eq1081 x
       grind)
    | exact superpose eq1081 eq320070
    | exact resolve eq320070 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320070
  have eq320138 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq320126
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq320126
    | exact resolve eq320126 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320126
  have eq321297 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 (σ (M.op x y)) X0 (σ x)
       have i₂ := eq320138
       grind)
    | exact superpose eq320138 eq8
    | exact resolve eq8 eq320138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320138
  have eq321307 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq321297 X0
       have i₂ := eq121582 X0
       grind)
    | exact superpose eq121582 eq321297
    | exact resolve eq321297 eq121582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121582 eq321297
  have eq324784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq299108 x
       have i₂ := eq321307 (σ y)
       grind)
    | exact superpose eq321307 eq299108
    | exact resolve eq299108 eq321307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299108 eq321307
  have eq324830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq324784
  have eq324971 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq324830
       grind)
    | exact superpose eq324830 eq14
    | (have r₁ := eq14
       have r₂ := eq324830
       grind)
    | exact resolve eq14 eq324830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324830
  have eq325012 : x = y := by grind
  clear eq324971
  have eq325037 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq325012
       grind)
    | exact superpose eq325012 eq14
    | exact resolve eq14 eq325012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325012
  have eq326352 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq325037
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq325037
    | exact resolve eq325037 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325037
  have eq326364 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq326352
       have i₂ := eq1081 x
       grind)
    | exact superpose eq1081 eq326352
    | exact resolve eq326352 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq326352
  have eq326369 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq326364
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq326364
    | exact resolve eq326364 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005 eq326364
  have eq326370 : False := by grind
  exact eq326370

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation3744 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3744 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 (M.op X0 X2) X3 (M.op x X1) X5
       have i₂ := eq8 X0 X1 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X3 X1) X4 (M.op X0 x)
       have i₂ := eq8 X0 X1 x X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq18 x X1 X2 X3 x
       have i₂ := eq8 X2 X1 x x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq21 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq17 X0 x X2 X3 x
       have i₂ := eq8 X0 X3 x x
       grind)
    | exact superpose eq8 eq17
    | exact resolve eq17 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq54 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq60 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (τ X1)) X2
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq111 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq33 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq33 X0 X1
       grind)
    | exact resolve eq11 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ X0) X2) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X1) (σ X0) X2
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq21
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq21 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq115 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq117 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq116
    | (have j0 := eq116 X0 X1
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq645 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq117 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq117
    | exact resolve eq117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq645
    | (have j0 := eq645 X0 X1
       grind)
    | exact resolve eq645 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq686 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq682 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq682
    | (have j0 := eq682 X0 X1
       grind)
    | exact resolve eq682 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq682
  have eq1011 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X2)) ∨ (σ X1) = (σ (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X2 X1
       have i₂ := eq114 X2 X0 (σ X1)
       grind)
    | (have i₁ := eq117 X1 X1
       have i₂ := eq114 X0 X1 (σ X1)
       grind)
    | exact superpose eq114 eq117
    | (have j0 := eq117 X2 X0
       have j1 := eq114 X2 X0 X2
       grind)
    | exact resolve eq117 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1058 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq3204 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq686
    | exact resolve eq686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq12361 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1058 (τ X0) (τ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq1058
    | exact resolve eq1058 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1058
  have eq12473 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12361 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12361
    | (have j0 := eq12361 X0 X1
       grind)
    | exact resolve eq12361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12361
  have eq12506 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12473 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq12473
    | (have j0 := eq12473 X0 X1
       grind)
    | exact resolve eq12473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12473
  have eq12527 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12506 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12506
    | (have j0 := eq12506 X0 X1
       grind)
    | exact resolve eq12506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12506
  have eq12533 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12527 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq12527
    | (have j0 := eq12527 X0 X1
       grind)
    | exact resolve eq12527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12527
  have eq12534 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12533 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq12533
    | (have j0 := eq12533 X0 X1
       grind)
    | exact resolve eq12533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12533
  have eq65100 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X1
       have i₂ := eq1011 X0 X1 X1
       grind)
    | exact superpose eq1011 eq115
    | (have j0 := eq115 X1
       have j1 := eq1011 X0 X1 X1
       grind)
    | (have r₁ := eq115 x
       have r₂ := eq1011 X0 x x
       grind)
    | exact resolve eq115 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq65501 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65100 X0 X1
       have j1 := eq115 X1
       grind)
    | (have r₁ := eq65100 X0 X0
       have r₂ := eq115 X0
       grind)
    | (have r₁ := eq65100 X0 X0
       have r₂ := eq115 X0
       grind)
    | exact resolve eq65100 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq65100
  have eq65882 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65501 X0 X1
       have j1 := eq33 X1 X0
       grind)
    | (have r₁ := eq65501 X1 X0
       have r₂ := eq33 X0 X1
       grind)
    | exact resolve eq65501 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq65501
  have eq259487 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12534 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X1 X0
       grind)
    | exact superpose eq8 eq12534
    | (have j0 := eq12534 (M.op X0 X1) X2
       grind)
    | exact resolve eq12534 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12534
  have eq259496 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq259487 X0 X1 X2
       have j1 := eq3204 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq259487 X0 X1 X0
       have r₂ := eq3204 X0 (M.op X0 X1)
       grind)
    | exact resolve eq259487 eq3204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3204 eq259487
  have eq259555 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259496 X0 X1 X2
       have i₂ := eq20 X1 X2 X0
       grind)
    | exact superpose eq20 eq259496
    | exact resolve eq259496 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq259496
  have eq284444 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65882 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65882
    | exact resolve eq65882 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65882
  have eq284523 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq284444 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq284444
    | (have j0 := eq284444 X0 X1
       grind)
    | exact resolve eq284444 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq284444
  have eq284538 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq284523 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq284523
    | (have j0 := eq284523 X1 X1
       grind)
    | exact resolve eq284523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284523
  have eq285202 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259555 X0 X0 X1
       have i₂ := eq284538 X2 X0
       grind)
    | exact superpose eq284538 eq259555
    | (have j1 := eq284538 X0 X1
       grind)
    | exact resolve eq259555 eq284538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284538
  have eq288960 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq285202 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285202
  have eq288961 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq288960 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288960
  have eq289404 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 (τ (σ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 (σ X0) X1
       have i₂ := eq288961 (σ X0)
       grind)
    | exact superpose eq288961 eq60
    | exact resolve eq60 eq288961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq289538 : ∀ X0 X1 : G, (σ (k (k X0 X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq289404 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq289404
    | exact resolve eq289404 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289404
  have eq289582 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq289538 X0 X1
       have i₂ := eq259555 (σ X0) (σ X0) (σ X1)
       grind)
    | exact superpose eq259555 eq289538
    | exact resolve eq289538 eq259555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289538
  have eq289601 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq289582 X0 X1
       have i₂ := eq288961 X0
       grind)
    | exact superpose eq288961 eq289582
    | exact resolve eq289582 eq288961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288961 eq289582
  have eq289612 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq289601 X0 X1
       have i₂ := eq259555 X0 X0 X1
       grind)
    | exact superpose eq259555 eq289601
    | exact resolve eq289601 eq259555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259555 eq289601
  have eq295822 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq289612 y x
       grind)
    | exact superpose eq289612 eq14
    | (have r₁ := eq14
       have r₂ := eq289612 y x
       grind)
    | exact resolve eq14 eq289612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289612
  have eq296004 : False := by grind
  exact eq296004

/-- `Equation3748`: `x ◇ y = (y ◇ x) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation3748 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3748 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3748.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
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
  have eq31 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq32
    | exact resolve eq32 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq33 (σ X0) (σ X1)
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 (σ X0) X1
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq33 X0 (τ X1)
       grind)
    | exact superpose eq33 eq16
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq16 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq122 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq107
    | exact resolve eq107 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq143 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X1 X0))) = (M.op (M.op X0 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op (M.op X1 X2) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) (M.op X1 X0)) X2) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq21 X0 X1
       grind)
    | (have i₁ := eq31 X0 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq31
    | (have j0 := eq31 X2 (M.op X0 X0) X2
       grind)
    | exact resolve eq31 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31
  have eq358 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq35 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq35
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X1 X0
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq13
    | (have j1 := eq35 X1 X0
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq35 X2 X0
       grind)
    | exact superpose eq35 eq13
    | (have j1 := eq35 X2 X0
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq974 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq99
    | (have j0 := eq99 X1 X1
       grind)
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1038 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq974 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq974
    | (have j0 := eq974 X0 X1
       grind)
    | exact resolve eq974 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1094 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X0
       have i₂ := eq1038 X1 X0
       grind)
    | exact superpose eq1038 eq68
    | (have j0 := eq68 X0 X0
       have j1 := eq1038 X1 X0
       grind)
    | (have r₁ := eq68 X1 X1
       have r₂ := eq1038 X0 X1
       grind)
    | exact resolve eq68 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1038
  have eq1103 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1094 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1254 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0
       have i₂ := eq1103 X0 X1
       grind)
    | exact superpose eq1103 eq409
    | (have j0 := eq409 X0
       have j1 := eq1103 X0 X1
       grind)
    | exact resolve eq409 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq1103
  have eq1281 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1254 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1936 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq61 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq2749 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq98 x y
       grind)
    | exact superpose eq98 eq14
    | (have j1 := eq98 x x
       grind)
    | exact resolve eq14 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq2804 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq1281 x x
       grind)
    | (have r₁ := eq2749
       have r₂ := eq1281 x y
       grind)
    | exact resolve eq2749 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq2749
  have eq2820 : x = (k x (τ (σ x))) := by
    first
    | (have i₁ := eq122 x
       have i₂ := eq2804
       grind)
    | exact superpose eq2804 eq122
    | exact resolve eq122 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq2842 : x = (k x x) := by
    first
    | (have i₁ := eq2820
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2820
    | exact resolve eq2820 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820
  have eq2950 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq2842
       grind)
    | exact superpose eq2842 eq33
    | (have j0 := eq33 x x
       grind)
    | exact resolve eq33 eq2842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2842
  have eq2954 : x = (M.op x x) := by grind
  clear eq2950
  have eq3018 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq19 x x
       have i₂ := eq2954
       grind)
    | exact superpose eq2954 eq19
    | exact resolve eq19 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3283 : ∀ X0 : G, (τ (σ x)) = X0 ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
    intro X0
    first
    | (have i₁ := eq385 x X0
       have i₂ := eq2804
       grind)
    | exact superpose eq2804 eq385
    | (have j0 := eq385 x X0
       grind)
    | exact resolve eq385 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq3381 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq3283 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq3283
    | (have j0 := eq3283 X0
       grind)
    | exact resolve eq3283 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3283
  have eq8831 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq386 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq386
    | exact resolve eq386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq9007 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8831 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq8831
    | (have j0 := eq8831 X0 X1 X2
       grind)
    | exact resolve eq8831 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8831
  have eq9357 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq387 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq387
    | exact resolve eq387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq9534 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9357 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9357
    | (have j0 := eq9357 X0 X1 X2
       grind)
    | exact resolve eq9357 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9357
  have eq20020 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) X0) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq143 X0 X1
       have i₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X1 X0))
       grind)
    | exact superpose eq12 eq143
    | (have j1 := eq12 X0 (M.op (M.op X1 X1) X0)
       grind)
    | exact resolve eq143 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq26463 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op X2 (M.op (M.op X1 X0) (M.op X0 X0))) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq148 X2 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq187 X0 X1 X2
       grind)
    | exact superpose eq187 eq148
    | (have j0 := eq148 X2 (M.op X0 X0) X2
       have j1 := eq187 X0 X1 X2
       grind)
    | exact resolve eq148 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq187
  have eq26588 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op X2 (M.op (M.op X1 X0) (M.op X0 X0))) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq26463 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26463
  have eq26647 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op X2 (M.op X0 X1)) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26588 X0 X1 X2
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq26588
    | (have j0 := eq26588 X0 X1 X2
       grind)
    | exact resolve eq26588 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26588
  have eq59050 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k X2 (σ (τ X0))) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9007 X2 (τ X0) (τ X1)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq9007
    | (have j0 := eq9007 X2 (τ X0) X2
       grind)
    | exact resolve eq9007 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9007
  have eq59085 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k X2 (σ (τ X0))) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59050 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq59050
    | (have j0 := eq59050 X0 X1 X2
       grind)
    | exact resolve eq59050 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59050
  have eq59091 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k X2 (σ (τ X0))) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59085 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq59085
    | (have j0 := eq59085 X0 X1 X2
       grind)
    | exact resolve eq59085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59085
  have eq59092 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (k X0 X1) = (k (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59091 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59091
    | (have j0 := eq59091 X0 X1 X2
       grind)
    | exact resolve eq59091 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59091
  have eq59175 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op (σ (τ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9534 X2 (τ X1) (τ X0)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq9534
    | (have j0 := eq9534 X2 (τ X1) X2
       grind)
    | exact resolve eq9534 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq9534
  have eq59218 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op (σ (τ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59175 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59175
    | (have j0 := eq59175 X0 X1 X2
       grind)
    | exact resolve eq59175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59175
  have eq59224 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op (σ (τ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59218 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq59218
    | (have j0 := eq59218 X0 X1 X2
       grind)
    | exact resolve eq59218 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59218
  have eq59225 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ (k X0 X1) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59224 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59224
    | (have j0 := eq59224 X0 X1 X2
       grind)
    | exact resolve eq59224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59224
  have eq59389 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ (M.op X0 X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq20020 X0 x
       have i₂ := eq2954
       grind)
    | exact superpose eq2954 eq20020
    | exact resolve eq20020 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20020
  have eq59710 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq59389 X0
       grind)
    | (have i₁ := eq8 X0 X0
       have i₂ := eq59389 X0
       grind)
    | exact superpose eq59389 eq8
    | (have j1 := eq59389 X0
       grind)
    | exact resolve eq8 eq59389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59389
  have eq59725 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq59710 X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq59710
    | (have j0 := eq59710 X0
       grind)
    | exact resolve eq59710 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59710
  have eq59867 : ∀ X0 X1 : G, (M.op X0 x) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k x X0) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq59725 X0
       grind)
    | (have i₁ := eq12 x X1
       have i₂ := eq59725 x
       grind)
    | exact superpose eq59725 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq59725 X0
       grind)
    | exact resolve eq12 eq59725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64761 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1936 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq64762 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq64761 X0 X1
       have j1 := eq358 X1 X0
       grind)
    | (have r₁ := eq64761 (k X1 X1) X0
       have r₂ := eq358 X0 X1
       grind)
    | (have r₁ := eq64761 X0 (σ (k X1 X1))
       have r₂ := eq358 (σ X0) X1
       grind)
    | (have r₁ := eq64761 X1 X0
       have r₂ := eq358 X0 X1
       grind)
    | exact resolve eq64761 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq64761
  have eq64831 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq64762 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq64762 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq64762 eq16
    | (have j1 := eq64762 (τ X1) X0
       grind)
    | exact resolve eq16 eq64762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq64762
  have eq64872 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64831 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq64831
    | (have j0 := eq64831 X0 X1
       grind)
    | exact resolve eq64831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64831
  have eq64884 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64872 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64872
    | (have j0 := eq64872 X0 X1
       grind)
    | exact resolve eq64872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64872
  have eq76962 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X1) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26647 X0 X0 (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq26647
    | exact resolve eq26647 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26647
  have eq76969 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76962 X0 X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq76962
    | (have j0 := eq76962 X0 X1
       grind)
    | exact resolve eq76962 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76962
  have eq84124 : ∀ X0 X1 : G, (k X0 X1) = (k x X1) ∨ (k x X0) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq59092 X0 X1 x
       have i₂ := eq2954
       grind)
    | exact superpose eq2954 eq59092
    | (have j0 := eq59092 X0 X1 x
       grind)
    | exact resolve eq59092 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59092
  have eq84874 : ∀ X0 : G, (k X0 X0) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq84124 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84124
  have eq85414 : ∀ X0 X1 : G, (M.op X1 x) ≠ X0 ∨ (M.op X1 x) = (k x X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq84874 X1
       have i₂ := eq64884 X0 X1
       grind)
    | (have i₁ := eq84874 X0
       have i₂ := eq64884 (k X0 X0) X1
       grind)
    | exact superpose eq64884 eq84874
    | (have j0 := eq84874 X1
       have j1 := eq64884 X1 x
       grind)
    | (have r₁ := eq84874 x
       have r₂ := eq64884 x x
       grind)
    | (have r₁ := eq84874 X1
       have r₂ := eq64884 (M.op X1 x) X1
       grind)
    | exact resolve eq84874 eq64884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64884
  have eq85487 : ∀ X0 X1 : G, (M.op X1 x) = (k x X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq85414 X0 X1
       have j1 := eq59867 X1 (k x X1)
       grind)
    | (have r₁ := eq85414 X1 X0
       have r₂ := eq59867 X0 X1
       grind)
    | (have r₁ := eq85414 (M.op X0 x) X1
       have r₂ := eq59867 X0 (M.op X1 x)
       grind)
    | (have r₁ := eq85414 (k x X1) X1
       have r₂ := eq59867 x X1
       grind)
    | exact resolve eq85414 eq59867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59867 eq85414
  have eq86454 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq84874 X0
       have i₂ := eq85487 X0 X0
       grind)
    | exact superpose eq85487 eq84874
    | (have j0 := eq84874 X0
       have j1 := eq85487 X0 X0
       grind)
    | (have r₁ := eq84874 x
       have r₂ := eq85487 X0 x
       grind)
    | (have r₁ := eq84874 x
       have r₂ := eq85487 x x
       grind)
    | exact resolve eq84874 eq85487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84874 eq85487
  have eq86587 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq86454 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86454
  have eq86611 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq86587 X0
       have j1 := eq59725 X0
       grind)
    | (have r₁ := eq86587 X0
       have r₂ := eq59725 X0
       grind)
    | (have r₁ := eq86587 x
       have r₂ := eq59725 x
       grind)
    | exact resolve eq86587 eq59725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59725 eq86587
  have eq93888 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59225 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59225
  have eq93889 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq93888
  have eq93972 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93889 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq93889
    | (have r₁ := eq93889 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq8 X1 X1
       grind)
    | exact resolve eq93889 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93889
  have eq94131 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93972 X0 X1
       have j1 := eq76969 X0 X1
       grind)
    | (have r₁ := eq93972 X0 X1
       have r₂ := eq76969 X0 X1
       grind)
    | (have r₁ := eq93972 X1 X1
       have r₂ := eq76969 X1 X1
       grind)
    | exact resolve eq93972 eq76969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76969 eq93972
  have eq94278 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (k (M.op (σ x) (σ x)) (σ (k x X0))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94131 (σ x) (σ X0)
       have i₂ := eq3381 X0
       grind)
    | exact superpose eq3381 eq94131
    | (have j1 := eq3381 X0
       grind)
    | exact resolve eq94131 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381 eq94131
  have eq94404 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (k (M.op (σ x) (σ x)) (σ (M.op X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94278 X0
       have i₂ := eq86611 X0
       grind)
    | exact superpose eq86611 eq94278
    | (have j0 := eq94278 X0
       grind)
    | exact resolve eq94278 eq86611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94278
  have eq94453 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (k (σ x) (σ (M.op X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94404 X0
       have i₂ := eq2804
       grind)
    | exact superpose eq2804 eq94404
    | (have j0 := eq94404 X0
       grind)
    | exact resolve eq94404 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94404
  have eq94477 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k x (M.op X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94453 X0
       have i₂ := eq13 x (M.op X0 x)
       grind)
    | exact superpose eq13 eq94453
    | (have j0 := eq94453 X0
       grind)
    | exact resolve eq94453 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94453
  have eq94486 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op (M.op X0 x) x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94477 X0
       have i₂ := eq86611 (M.op X0 x)
       grind)
    | exact superpose eq86611 eq94477
    | (have j0 := eq94477 X0
       grind)
    | exact resolve eq94477 eq86611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86611 eq94477
  have eq94489 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94486 X0
       have i₂ := eq3018 X0
       grind)
    | exact superpose eq3018 eq94486
    | (have j0 := eq94486 X0
       grind)
    | exact resolve eq94486 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018 eq94486
  have eq95047 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq94489 y
       grind)
    | exact superpose eq94489 eq14
    | (have j1 := eq94489 y
       grind)
    | (have r₁ := eq14
       have r₂ := eq94489 y
       grind)
    | exact resolve eq14 eq94489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94489
  have eq95070 : x = y := by grind
  clear eq95047
  have eq95079 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq95070
       grind)
    | exact superpose eq95070 eq14
    | exact resolve eq14 eq95070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95070
  have eq95225 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq95079
       have i₂ := eq2954
       grind)
    | exact superpose eq2954 eq95079
    | exact resolve eq95079 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954 eq95079
  have eq95226 : False := by grind
  exact eq95226

/-- `Equation3751`: `x ◇ y = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3751 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3751 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3751.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq118 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq30 X1 (τ X0)
       grind)
    | exact superpose eq30 eq16
    | (have j1 := eq30 X1 X1
       grind)
    | exact resolve eq16 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq124 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq40
  have eq139 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq124
    | exact resolve eq124 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq234 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq9
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq888 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq118
    | (have j0 := eq118 X0 X1
       grind)
    | exact resolve eq118 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq953 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq888
    | (have j0 := eq888 X0 X1
       grind)
    | exact resolve eq888 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq1124 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1212 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1124 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1124
    | (have j0 := eq1124 X0 X1
       grind)
    | exact resolve eq1124 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq2165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq234
       have i₂ := eq1212 y x
       grind)
    | exact superpose eq1212 eq234
    | (have j1 := eq1212 (σ y) (σ x)
       grind)
    | (have r₁ := eq234
       have r₂ := eq1212 y x
       grind)
    | exact resolve eq234 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq2166 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq234
       have i₂ := eq953 x y
       grind)
    | exact superpose eq953 eq234
    | (have j1 := eq953 x y
       grind)
    | (have r₁ := eq234
       have r₂ := eq953 x y
       grind)
    | exact resolve eq234 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq2167 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2166
  have eq2168 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2165
  have eq2194 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq50 (σ x) (σ x)
       have i₂ := eq2167
       grind)
    | exact superpose eq2167 eq50
    | exact resolve eq50 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2167
  have eq2200 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2194
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq2194
    | exact resolve eq2194 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq3024 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq2200
       grind)
    | exact superpose eq2200 eq9
    | exact resolve eq9 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq3072 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3024
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3024
    | exact resolve eq3024 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3024
  have eq3073 : y = (k y y) := by
    first
    | (have j1 := eq84 y y
       grind)
    | (have r₁ := eq3072
       have r₂ := eq84 y y
       grind)
    | exact resolve eq3072 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq3072
  have eq3252 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq264 y
       have i₂ := eq3073
       grind)
    | exact superpose eq3073 eq264
    | (have j0 := eq264 y
       grind)
    | exact resolve eq264 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq3259 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq30 y y
       have i₂ := eq3073
       grind)
    | exact superpose eq3073 eq30
    | (have j0 := eq30 y x
       grind)
    | exact resolve eq30 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3073
  have eq3263 : y = (M.op y y) := by grind
  clear eq3259
  have eq3266 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3252
  have eq3351 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq49 y y x
       have i₂ := eq3263
       grind)
    | exact superpose eq3263 eq49
    | (have j0 := eq49 y X0 (k y X0)
       grind)
    | exact resolve eq49 eq3263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3263
  have eq3557 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq246 y X0
       have i₂ := eq3266
       grind)
    | exact superpose eq3266 eq246
    | (have j0 := eq246 y X0
       grind)
    | exact resolve eq246 eq3266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq3586 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq3557 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3557
    | (have j0 := eq3557 X0
       grind)
    | exact resolve eq3557 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557
  have eq5188 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq139 x
       have i₂ := eq2168
       grind)
    | exact superpose eq2168 eq139
    | exact resolve eq139 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq2168
  have eq5210 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5188
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5188
    | exact resolve eq5188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5188
  have eq5426 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq5210
       grind)
    | exact superpose eq5210 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq5210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5210
  have eq5437 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq5426
  have eq5832 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq5437
       grind)
    | exact superpose eq5437 eq18
    | exact resolve eq18 eq5437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5437
  have eq6258 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq5832
  have eq15379 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq48 (σ X0) (σ y)
       have i₂ := eq3586 X0
       grind)
    | exact superpose eq3586 eq48
    | (have j1 := eq3586 X0
       grind)
    | exact resolve eq48 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq15827 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq15379 x
       grind)
    | exact superpose eq15379 eq14
    | (have j1 := eq15379 x
       grind)
    | exact resolve eq14 eq15379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15379
  have eq16181 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq15827
       have i₂ := eq3351 x
       grind)
    | exact superpose eq3351 eq15827
    | (have j1 := eq3351 x
       grind)
    | exact resolve eq15827 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351
  have eq16190 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15827
       have i₂ := eq953 y x
       grind)
    | exact superpose eq953 eq15827
    | (have j1 := eq953 x x
       grind)
    | exact resolve eq15827 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq15827
  have eq16195 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y := by grind
  clear eq16181
  have eq16200 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq16190
       have r₂ := eq6258
       grind)
    | exact resolve eq16190 eq6258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6258 eq16190
  have eq16215 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq16195
       have i₂ := eq48 y x
       grind)
    | (have i₁ := eq16195
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16195
    | exact resolve eq16195 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16195
  have eq16216 : x = y := by grind
  clear eq16215
  have eq16219 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16200
       have i₂ := eq48 y x
       grind)
    | (have i₁ := eq16200
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16200
    | exact resolve eq16200 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq16200
  have eq16220 : x = (M.op x x) := by grind
  clear eq16219
  have eq16444 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq16216
       grind)
    | exact superpose eq16216 eq14
    | exact resolve eq14 eq16216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16457 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3266
       have i₂ := eq16216
       grind)
    | exact superpose eq16216 eq3266
    | exact resolve eq3266 eq16216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3266 eq16216
  have eq16479 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16444
       have i₂ := eq16220
       grind)
    | exact superpose eq16220 eq16444
    | exact resolve eq16444 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16220 eq16444
  have eq16480 : False := by grind
  exact eq16480

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation3756 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3756 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X1 X0) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op x x) X1
       have i₂ := eq8 x x x
       grind)
    | exact superpose eq8 eq11
    | (have r₁ := eq11 (M.op x x) X1
       have r₂ := eq8 x x x
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X0
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq51 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 X0) X1
       have i₂ := eq33 X0 (σ X1)
       grind)
    | exact superpose eq33 eq20
    | exact resolve eq20 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq23 X1 X1 X0
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq93 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq64 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq11
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq64 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq64 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq46 X0 (σ X1) X2
       grind)
    | exact superpose eq46 eq20
    | (have j1 := eq46 (τ X0) X1 X2
       grind)
    | exact resolve eq20 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq154 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (k (M.op X0 X1) X3) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 X0 x
       have i₂ := eq38 (M.op X0 X1) x X3
       grind)
    | exact superpose eq38 eq8
    | (have j1 := eq38 (M.op X0 X1) X1 X3
       grind)
    | exact resolve eq8 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq192 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k (M.op X1 X0) X2) ∨ (M.op (M.op X1 X0) X3) = (k (M.op X1 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (M.op X2 X1) X1
       have i₂ := eq41 (M.op X2 X1) X1 X2 X3
       grind)
    | exact superpose eq41 eq11
    | (have j1 := eq41 (M.op X1 X0) X1 X2 X3
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq41 (M.op X1 X1) X1 X1 X3
       grind)
    | exact resolve eq11 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq207 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X1 X0) X2) ∨ (M.op (M.op X1 X0) X3) = (k (M.op X1 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq192 X0 X1 X2 X3
       have j1 := eq154 X1 X0 X3
       grind)
    | (have r₁ := eq192 X0 X1 X2 X3
       have r₂ := eq154 X0 X1 X3
       grind)
    | (have r₁ := eq192 X1 X0 X2 X3
       have r₂ := eq154 X0 X1 X3
       grind)
    | exact resolve eq192 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq192
  have eq238 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X0
       have i₂ := eq64 (σ X0) X1
       grind)
    | (have i₁ := eq44 X0 X0
       have i₂ := eq64 X0 (σ X0)
       grind)
    | exact superpose eq64 eq44
    | exact resolve eq44 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq245 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq14
    | (have j1 := eq44 x x
       grind)
    | exact resolve eq14 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq890 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X1 (M.op X0 X0)
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq238
    | (have j0 := eq238 X1 (M.op X0 X0)
       grind)
    | exact resolve eq238 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq930 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq238 X0 (τ X1)
       grind)
    | exact superpose eq238 eq16
    | (have j1 := eq238 X0 (τ X1)
       grind)
    | exact resolve eq16 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq238
  have eq955 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq890 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq963 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq930 X0 X1
       have j1 := eq93 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq930 X0 X1
       have r₂ := eq93 X0 (k (σ (τ X1)) X1) x
       grind)
    | (have r₁ := eq930 X0 X1
       have r₂ := eq93 X0 (σ (τ X1)) x
       grind)
    | exact resolve eq930 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq930
  have eq977 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq963 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq963
    | exact resolve eq963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq985 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | (have j0 := eq42 X1 X1
       grind)
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq1055 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq985
    | (have j0 := eq985 X0 X1
       grind)
    | exact resolve eq985 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1066 : ∀ X0 X2 : G, (k X0 X0) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq977 x X2
       have i₂ := eq977 x X0
       grind)
    | exact superpose eq977 eq977
    | exact resolve eq977 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1134 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq977 X0 (σ X1)
       grind)
    | exact superpose eq977 eq13
    | exact resolve eq13 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1141 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 X1
       have i₂ := eq977 X0 (τ X1)
       grind)
    | exact superpose eq977 eq47
    | exact resolve eq47 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1143 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X1)
       have i₂ := eq977 X0 (τ X1)
       grind)
    | exact superpose eq977 eq15
    | exact resolve eq15 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq1146 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1143 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1143
    | exact resolve eq1143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq2357 : ∀ X0 X2 : G, (k X2 X2) = (σ (σ (k X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq1146 x X2
       have i₂ := eq1134 x X0
       grind)
    | exact superpose eq1134 eq1146
    | exact resolve eq1146 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq1146
  have eq3118 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq245
       have i₂ := eq46 x X0 y
       grind)
    | exact superpose eq46 eq245
    | (have j1 := eq46 x X0 x
       grind)
    | exact resolve eq245 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq245
  have eq3122 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq3118 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118
  have eq8086 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X1 X0) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq207 X1 X0 X2 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq20292 : ∀ X0 X1 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ x) X1
       have i₂ := eq3122 X0
       grind)
    | exact superpose eq3122 eq51
    | (have j1 := eq3122 X1
       grind)
    | exact resolve eq51 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq3122
  have eq20427 : ∀ X0 X1 : G, x = (k x X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20292 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq20292
    | (have j0 := eq20292 X0 X0
       grind)
    | exact resolve eq20292 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20292
  have eq20607 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq20427 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20427
  have eq20608 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq20607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20607
  have eq20949 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq977 X0 x
       have i₂ := eq20608 x
       grind)
    | exact superpose eq20608 eq977
    | exact resolve eq977 eq20608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq20951 : ∀ X0 : G, x = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1066 X0 x
       have i₂ := eq20608 x
       grind)
    | exact superpose eq20608 eq1066
    | exact resolve eq1066 eq20608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq20969 : ∀ X0 : G, (k X0 X0) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2357 x X0
       have i₂ := eq20608 x
       grind)
    | exact superpose eq20608 eq2357
    | exact resolve eq2357 eq20608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357 eq20608
  have eq21530 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq20949 x
       grind)
    | exact superpose eq20949 eq8
    | exact resolve eq8 eq20949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21567 : ∀ X1 : G, x = (τ (k X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq1141 x X1
       have i₂ := eq20949 x
       grind)
    | exact superpose eq20949 eq1141
    | exact resolve eq1141 eq20949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq21722 : x = (τ (σ (σ x))) := by
    first
    | (have i₁ := eq21567 x
       have i₂ := eq20969 x
       grind)
    | exact superpose eq20969 eq21567
    | exact resolve eq21567 eq20969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20969 eq21567
  have eq21797 : x = (σ x) := by
    first
    | (have i₁ := eq21722
       have i₂ := eq9 (σ x)
       grind)
    | exact superpose eq9 eq21722
    | exact resolve eq21722 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21722
  have eq22328 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21797
       grind)
    | exact superpose eq21797 eq14
    | exact resolve eq14 eq21797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22331 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq21797
       grind)
    | exact superpose eq21797 eq13
    | exact resolve eq13 eq21797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21797
  have eq22640 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20949 X0
       have i₂ := eq1055 X1 X0
       grind)
    | exact superpose eq1055 eq20949
    | (have j1 := eq1055 X1 X0
       grind)
    | exact resolve eq20949 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055 eq20949
  have eq24121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 (τ X0) X1
       have i₂ := eq20951 (τ X0)
       grind)
    | exact superpose eq20951 eq107
    | (have j0 := eq107 X0 X1 X1
       grind)
    | exact resolve eq107 eq20951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq20951
  have eq75785 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8086 X1 X0 x
       have i₂ := eq21530 X0 X1
       grind)
    | exact superpose eq21530 eq8086
    | (have j0 := eq8086 X1 X0 x
       grind)
    | (have r₁ := eq8086 X1 X0 x
       have r₂ := eq21530 X0 X1
       grind)
    | exact resolve eq8086 eq21530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8086 eq21530
  have eq75833 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have j0 := eq75785 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75785
  have eq330806 : ∀ X0 : G, (M.op (σ X0) x) = (σ (k X0 x)) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq22331 X0
       have i₂ := eq24121 (σ X0) x
       grind)
    | exact superpose eq24121 eq22331
    | (have j1 := eq24121 (σ X0) x
       grind)
    | exact resolve eq22331 eq24121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24121
  have eq330885 : ∀ X0 : G, (M.op (σ X0) x) = (σ (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq330806 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq330806
    | (have j0 := eq330806 X0
       grind)
    | exact resolve eq330806 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330806
  have eq530150 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq22640 X0 x
       have i₂ := eq330885 X0
       grind)
    | exact superpose eq330885 eq22640
    | (have j0 := eq22640 X0 x
       have j1 := eq330885 X0
       grind)
    | exact resolve eq22640 eq330885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22640 eq330885
  have eq530175 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq530150 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530150
  have eq534164 : ∀ X0 : G, (k (M.op (σ X0) x) x) = (σ (k (M.op X0 x) x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq22331 (M.op X0 x)
       have i₂ := eq530175 X0
       grind)
    | exact superpose eq530175 eq22331
    | (have j1 := eq530175 X0
       grind)
    | exact resolve eq22331 eq530175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22331 eq530175
  have eq534167 : ∀ X0 : G, (σ (M.op x X0)) = (k (M.op (σ X0) x) x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq534164 X0
       have i₂ := eq75833 x X0
       grind)
    | exact superpose eq75833 eq534164
    | (have j0 := eq534164 X0
       grind)
    | exact resolve eq534164 eq75833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534164
  have eq534175 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq534167 X0
       have i₂ := eq75833 x (σ X0)
       grind)
    | exact superpose eq75833 eq534167
    | (have j0 := eq534167 X0
       grind)
    | exact resolve eq534167 eq75833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75833 eq534167
  have eq536926 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq22328
       have i₂ := eq534175 y
       grind)
    | exact superpose eq534175 eq22328
    | (have j1 := eq534175 y
       grind)
    | (have r₁ := eq22328
       have r₂ := eq534175 y
       grind)
    | exact resolve eq22328 eq534175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22328 eq534175
  have eq536943 : x = y := by grind
  clear eq536926
  have eq538101 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq536943
       grind)
    | exact superpose eq536943 eq14
    | exact resolve eq14 eq536943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536943
  have eq538107 : False := by grind
  exact eq538107

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_y_pxy_Equation3756 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3756 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X1 X0) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq8 X0 X0 X0
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq11 (M.op x x) X1
       have r₂ := eq8 x x x
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq19 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq17
    | exact resolve eq17 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X2) = (k X0 X2) := by
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
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (k X0 X1) = X1 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1)
       have i₂ := eq20 X1 (τ X0)
       grind)
    | exact superpose eq20 eq16
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38
    | exact resolve eq38 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X2 X1 X0
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq21 X1 X1 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq111 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (k (τ X1) X2) = (M.op (τ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq31 (τ X1) X0 X2
       grind)
    | exact superpose eq31 eq15
    | (have j1 := eq31 X1 (σ X0) X2
       grind)
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq31 X0 X2 (τ X1)
       grind)
    | exact superpose eq31 eq16
    | (have j1 := eq31 X0 X2 X2
       grind)
    | exact resolve eq16 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq63 (σ X0) X1
       grind)
    | (have i₁ := eq29 X0 X0
       have i₂ := eq63 X0 (σ X0)
       grind)
    | exact superpose eq63 eq29
    | exact resolve eq29 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x x
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq894 : ∀ X0 X1 X2 : G, (k (k (σ (τ X0)) X0) X1) = X1 ∨ (k (τ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq112 (τ X0) X0 X2
       grind)
    | exact superpose eq112 eq47
    | (have j1 := eq112 (k (σ (τ X0)) X0) X1 X1
       grind)
    | exact resolve eq47 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq112
  have eq941 : ∀ X0 X1 X2 : G, (k (k X0 X0) X1) = X1 ∨ (k (τ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq894 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq894
    | (have j0 := eq894 X0 X1 X2
       grind)
    | exact resolve eq894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1059 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq293 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq293
    | (have j0 := eq293 (τ X0)
       grind)
    | exact resolve eq293 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq1071 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1059 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1059
    | (have j0 := eq1059 X0
       grind)
    | exact resolve eq1059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1078 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1071 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1071
    | (have j0 := eq1071 X0
       grind)
    | exact resolve eq1071 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1451 : ∀ X0 X1 X2 X3 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X2 (τ (σ X0))))) ∨ (k (τ (σ X2)) X3) = (M.op (τ (σ X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq42 X2 (σ X0) X1
       have i₂ := eq111 X0 (σ X2) X3
       grind)
    | exact superpose eq111 eq42
    | (have j1 := eq111 X0 (σ X2) X3
       grind)
    | exact resolve eq42 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq111
  have eq1481 : ∀ X0 X1 X2 X3 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X2 X0))) ∨ (k (τ (σ X2)) X3) = (M.op (τ (σ X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1451 X0 X1 X2 X3
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1451
    | (have j0 := eq1451 X0 X1 X2 X3
       grind)
    | exact resolve eq1451 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq1499 : ∀ X0 X1 X2 X3 : G, (σ (k X1 X0)) = (σ (k X1 (k X2 X0))) ∨ (k (τ (σ X2)) X3) = (M.op (τ (σ X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1481 X0 X1 X2 X3
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1481
    | (have j0 := eq1481 X0 X1 X2 X3
       grind)
    | exact resolve eq1481 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481
  have eq1502 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (k X2 X3) ∨ (σ (k X1 X0)) = (σ (k X1 (k X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1499 X0 X1 X0 X3
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1499
    | (have j0 := eq1499 X0 X1 X2 X3
       grind)
    | exact resolve eq1499 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq2042 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k (k X1 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (τ X1)
       have i₂ := eq941 X1 X2 (τ X0)
       grind)
    | exact superpose eq941 eq16
    | (have j1 := eq941 X1 X2 X2
       grind)
    | exact resolve eq16 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq2045 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X1 X0) ∨ (k (k X1 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2042 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2042
    | (have j0 := eq2042 X0 X1 X2
       grind)
    | exact resolve eq2042 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042
  have eq2061 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k (k X1 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2045 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2045
    | (have j0 := eq2045 X0 X1 X2
       grind)
    | exact resolve eq2045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq2500 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq265
       have i₂ := eq31 x X0 y
       grind)
    | exact superpose eq31 eq265
    | (have j1 := eq31 x X0 x
       grind)
    | exact resolve eq265 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq265
  have eq2503 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2500 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500
  have eq2558 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq2503 (τ X0)
       grind)
    | exact superpose eq2503 eq16
    | exact resolve eq16 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq2561 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2558 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2558
    | exact resolve eq2558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558
  have eq2574 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2561 X0
       have j1 := eq11 (σ x) X0
       grind)
    | (have r₁ := eq2561 X0
       have r₂ := eq11 (σ x) x
       grind)
    | exact resolve eq2561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2725 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (σ x) X0
       have i₂ := eq2574 (σ X0)
       grind)
    | exact superpose eq2574 eq36
    | exact resolve eq36 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2730 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq2725 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2725
    | exact resolve eq2725 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2737 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2730 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2730
    | exact resolve eq2730 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq3047 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1078 x
       have i₂ := eq2737 x
       grind)
    | exact superpose eq2737 eq1078
    | (have j0 := eq1078 x
       grind)
    | (have r₁ := eq1078 x
       have r₂ := eq2737 x
       grind)
    | exact resolve eq1078 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3061 : ∀ X0 : G, (τ (σ X0)) = (k (τ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 x X0
       have i₂ := eq2737 (σ X0)
       grind)
    | exact superpose eq2737 eq36
    | exact resolve eq36 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2737
  have eq3064 : x = (M.op x x) := by grind
  clear eq3047
  have eq3066 : ∀ X0 : G, (k (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3061 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3061
    | exact resolve eq3061 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061
  have eq3102 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq3064
       grind)
    | exact superpose eq3064 eq8
    | exact resolve eq8 eq3064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3111 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq63 X0 x
       have i₂ := eq3064
       grind)
    | exact superpose eq3064 eq63
    | exact resolve eq63 eq3064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq3123 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 x x x
       have i₂ := eq3064
       grind)
    | exact superpose eq3064 eq58
    | (have j0 := eq58 X0 X1 x X1
       grind)
    | exact resolve eq58 eq3064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq3064
  have eq3686 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq1078 (τ x)
       have i₂ := eq3066 (τ x)
       grind)
    | exact superpose eq3066 eq1078
    | (have j0 := eq1078 (τ x)
       grind)
    | (have r₁ := eq1078 (τ x)
       have r₂ := eq3066 (τ x)
       grind)
    | exact resolve eq1078 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq3066
  have eq3705 : (τ x) = (M.op (τ x) (τ x)) := by grind
  clear eq3686
  have eq3717 : x = (τ x) := by
    first
    | (have i₁ := eq3705
       have i₂ := eq3111 (τ x)
       grind)
    | exact superpose eq3111 eq3705
    | exact resolve eq3705 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3705
  have eq3923 : x = (σ x) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq3717
       grind)
    | exact superpose eq3717 eq10
    | exact resolve eq10 eq3717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3925 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0
       have i₂ := eq3717
       grind)
    | exact superpose eq3717 eq16
    | exact resolve eq16 eq3717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq3717
  have eq4106 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3923
       grind)
    | exact superpose eq3923 eq14
    | exact resolve eq14 eq3923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3923
  have eq19960 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X1)
       have i₂ := eq258 X0 (τ X1)
       grind)
    | exact superpose eq258 eq15
    | (have j1 := eq258 X0 (τ X1)
       grind)
    | exact resolve eq15 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq258
  have eq20082 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19960 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq19960
    | (have j0 := eq19960 X0 X1
       grind)
    | exact resolve eq19960 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19960
  have eq20292 : ∀ X0 X1 : G, x = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20082 X0 X1
       have i₂ := eq3111 X0
       grind)
    | exact superpose eq3111 eq20082
    | (have j0 := eq20082 X0 X1
       grind)
    | exact resolve eq20082 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20082
  have eq20405 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ x = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20292 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq20292
    | (have j0 := eq20292 X0 X1
       grind)
    | exact resolve eq20292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20292
  have eq20443 : ∀ X1 : G, x = (k X1 X1) ∨ x = X1 := by
    intro X1
    first
    | (have i₁ := eq20405 x X1
       have i₂ := eq3111 x
       grind)
    | exact superpose eq3111 eq20405
    | (have j0 := eq20405 x X1
       grind)
    | exact resolve eq20405 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111 eq20405
  have eq20642 : ∀ X0 X1 : G, x = (k X0 X0) ∨ (k X0 X1) = X1 ∨ x = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2061 X1 X0 (k X0 X0)
       have i₂ := eq20443 (k X0 X0)
       grind)
    | exact superpose eq20443 eq2061
    | (have j0 := eq2061 X1 X0 x
       have j1 := eq20443 X0
       grind)
    | exact resolve eq2061 eq20443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061
  have eq20649 : ∀ X0 X1 : G, x = (k X0 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20642 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20642
  have eq26657 : ∀ X0 : G, x ≠ X0 ∨ x = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq20649 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20649
  have eq26663 : ∀ X0 : G, x = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq26657 X0
       have j1 := eq20443 X0
       grind)
    | (have r₁ := eq26657 (k x x)
       have r₂ := eq20443 x
       grind)
    | (have r₁ := eq26657 x
       have r₂ := eq20443 x
       grind)
    | (have r₁ := eq26657 x
       have r₂ := eq20443 x
       grind)
    | exact resolve eq26657 eq20443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20443 eq26657
  have eq92368 : ∀ X0 X1 X2 X3 : G, (τ (σ (k X0 X1))) = (k X0 (k X2 X1)) ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (k X0 (k X2 X1))
       have i₂ := eq1502 X1 X0 X2 X3
       grind)
    | exact superpose eq1502 eq9
    | (have j1 := eq1502 X0 X1 X2 X3
       grind)
    | exact resolve eq9 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq92505 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (k X0 (k X2 X1)) ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92368 X0 X1 X2 X3
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq92368
    | (have j0 := eq92368 X0 X1 X2 X3
       grind)
    | exact resolve eq92368 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92368
  have eq1886726 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 x) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92505 X0 X1 X1 X2
       have i₂ := eq26663 X1
       grind)
    | exact superpose eq26663 eq92505
    | (have j0 := eq92505 X0 X1 X1 X2
       grind)
    | exact resolve eq92505 eq26663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92505
  have eq1889942 : ∀ X0 : G, (k X0 X0) ≠ (M.op X0 x) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1886726 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886726
  have eq1889945 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq1889942 X0
       have i₂ := eq26663 X0
       grind)
    | exact superpose eq26663 eq1889942
    | (have j0 := eq1889942 X0
       grind)
    | exact resolve eq1889942 eq26663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26663 eq1889942
  have eq1890113 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1889945 X0
       have j1 := eq3123 X0 x
       grind)
    | (have r₁ := eq1889945 X0
       have r₂ := eq3123 X0 x
       grind)
    | exact resolve eq1889945 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123 eq1889945
  have eq1892142 : ∀ X0 : G, (M.op (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq3925 X0
       have i₂ := eq1890113 (σ X0)
       grind)
    | exact superpose eq1890113 eq3925
    | exact resolve eq3925 eq1890113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1892491 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1892142 X0
       have i₂ := eq1890113 X0
       grind)
    | exact superpose eq1890113 eq1892142
    | exact resolve eq1892142 eq1890113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892142
  have eq1896392 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X1 X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq1892491 (M.op X1 X0)
       have i₂ := eq3102 X0 X1
       grind)
    | exact superpose eq3102 eq1892491
    | exact resolve eq1892491 eq3102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896612 : ∀ X0 : G, (k (M.op (σ X0) x) x) = (σ (k (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq3925 (M.op X0 x)
       have i₂ := eq1892491 X0
       grind)
    | exact superpose eq1892491 eq3925
    | exact resolve eq3925 eq1892491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3925
  have eq1896640 : ∀ X0 : G, (k (M.op (σ X0) x) x) = (σ (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq1896612 X0
       have i₂ := eq1890113 (M.op X0 x)
       grind)
    | exact superpose eq1890113 eq1896612
    | exact resolve eq1896612 eq1890113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896612
  have eq1896787 : ∀ X0 : G, (k (M.op (σ X0) x) x) = (M.op (σ (M.op X0 x)) x) := by
    intro X0
    first
    | (have i₁ := eq1896640 X0
       have i₂ := eq1892491 (M.op X0 x)
       grind)
    | exact superpose eq1892491 eq1896640
    | exact resolve eq1896640 eq1892491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892491 eq1896640
  have eq1896862 : ∀ X0 : G, (σ (M.op x X0)) = (k (M.op (σ X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq1896787 X0
       have i₂ := eq1896392 x X0
       grind)
    | exact superpose eq1896392 eq1896787
    | exact resolve eq1896787 eq1896392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896392 eq1896787
  have eq1896885 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq1896862 X0
       have i₂ := eq1890113 (M.op (σ X0) x)
       grind)
    | exact superpose eq1890113 eq1896862
    | exact resolve eq1896862 eq1890113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890113 eq1896862
  have eq1896895 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1896885 X0
       have i₂ := eq3102 x (σ X0)
       grind)
    | exact superpose eq3102 eq1896885
    | exact resolve eq1896885 eq3102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102 eq1896885
  have eq1903003 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq4106
       have i₂ := eq1896895 y
       grind)
    | exact superpose eq1896895 eq4106
    | (have r₁ := eq4106
       have r₂ := eq1896895 y
       grind)
    | exact resolve eq4106 eq1896895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106 eq1896895
  have eq1903097 : False := by grind
  exact eq1903097

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pyx_Equation3756 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3756 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X1 X0) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
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
  clear eq16
  have eq34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X2 X1 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq21 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq21 X1 X1 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq96 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq160 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (M.op X0 X0)
       have i₂ := eq96 X0 (σ X1)
       grind)
    | exact superpose eq96 eq42
    | exact resolve eq42 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq68 (σ X0) X1
       grind)
    | (have i₁ := eq34 X0 X0
       have i₂ := eq68 X0 (σ X0)
       grind)
    | exact superpose eq68 eq34
    | exact resolve eq34 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq34 X2 X0
       grind)
    | exact superpose eq34 eq13
    | (have j1 := eq34 X2 X0
       grind)
    | exact resolve eq13 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X1 (σ X2)
       have i₂ := eq34 X0 X2
       grind)
    | exact superpose eq34 eq68
    | (have j1 := eq34 X0 X2
       grind)
    | exact resolve eq68 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq359 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X2)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq332 X0 X1 X2
       have i₂ := eq96 (σ X0) (σ X1)
       grind)
    | exact superpose eq96 eq332
    | (have j0 := eq332 X0 X1 X2
       grind)
    | exact resolve eq332 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq467 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (τ (M.op X0 X0))
       have i₂ := eq160 X0 (σ X1)
       grind)
    | exact superpose eq160 eq42
    | exact resolve eq42 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq160
  have eq991 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq467 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq467 eq300
    | (have j0 := eq300 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq300 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq992 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X1 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq300
    | (have j0 := eq300 X1 (M.op X0 X0)
       grind)
    | exact resolve eq300 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1029 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq300 X0 (τ X1)
       grind)
    | exact superpose eq300 eq17
    | (have j1 := eq300 X0 (τ X1)
       grind)
    | exact resolve eq17 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq1046 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq992 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1047 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq991 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1061 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1029 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1029
    | (have j0 := eq1029 X0 X1
       grind)
    | exact resolve eq1029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1071 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1047 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq1047
    | exact resolve eq1047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1074 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1061 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1061
    | (have j0 := eq1061 X0 X1
       grind)
    | exact resolve eq1061 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1328 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1071 x X1
       have i₂ := eq1071 X0 x
       grind)
    | exact superpose eq1071 eq1071
    | exact resolve eq1071 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1403 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1509 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1403 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1403
    | (have j0 := eq1403 X0 X1
       grind)
    | exact resolve eq1403 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq9547 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (k (σ X1) X2) ∨ (M.op (σ (τ X2)) (σ X0)) = (σ (k X0 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 X1
       have i₂ := eq359 X0 X1 (τ X2)
       grind)
    | exact superpose eq359 eq17
    | (have j1 := eq359 X0 X1 (τ X2)
       grind)
    | exact resolve eq17 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq9711 : ∀ X0 X1 X2 : G, (k (σ X0) X2) = (M.op (σ (τ X2)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9547 X0 X1 X2
       have i₂ := eq17 X2 X0
       grind)
    | exact superpose eq17 eq9547
    | (have j0 := eq9547 X0 X1 X2
       grind)
    | exact resolve eq9547 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq9547
  have eq9774 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (k (σ X0) X2) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9711 X0 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq9711
    | (have j0 := eq9711 X0 X1 X2
       grind)
    | exact resolve eq9711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9711
  have eq9870 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X1 X2
       have i₂ := eq1074 X2 X0
       grind)
    | exact superpose eq1074 eq68
    | (have j1 := eq1074 X1 X0
       grind)
    | exact resolve eq68 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1074
  have eq12152 : ∀ X0 X2 X3 : G, (k X2 X0) = X0 ∨ (M.op X3 X3) = (k X0 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq96 X2 x
       have i₂ := eq9870 X0 x X2
       grind)
    | (have i₁ := eq96 X0 x
       have i₂ := eq9870 (M.op X0 X0) x X2
       grind)
    | exact superpose eq9870 eq96
    | (have j1 := eq9870 X0 X3 X2
       grind)
    | exact resolve eq96 eq9870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq13496 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12152 X0 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12152
  have eq13506 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13496 X0 X1
       have j1 := eq9870 X0 X1 x
       grind)
    | (have r₁ := eq13496 (k X0 X0) X1
       have r₂ := eq9870 X0 X1 x
       grind)
    | (have r₁ := eq13496 X0 x
       have r₂ := eq9870 X0 X1 x
       grind)
    | (have r₁ := eq13496 (M.op x x) X1
       have r₂ := eq9870 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq13496 eq9870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9870 eq13496
  have eq14216 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1328 x X1
       have i₂ := eq13506 X0 x
       grind)
    | exact superpose eq13506 eq1328
    | exact resolve eq1328 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq14360 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 X1
       have i₂ := eq13506 (τ X1) X0
       grind)
    | exact superpose eq13506 eq51
    | exact resolve eq51 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq13506
  have eq37974 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1046 X2 X1
       have i₂ := eq1509 X0 X2
       grind)
    | (have i₁ := eq1046 X0 X1
       have i₂ := eq1509 (M.op X0 X0) X1
       grind)
    | exact superpose eq1509 eq1046
    | (have j1 := eq1509 X0 X2
       grind)
    | exact resolve eq1046 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046 eq1509
  have eq55782 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq346 x X0 y
       grind)
    | exact superpose eq346 eq14
    | (have j1 := eq346 x X0 x
       grind)
    | exact resolve eq14 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq55990 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq55782 X0
       have j1 := eq37974 x X0 x
       grind)
    | (have r₁ := eq55782 X0
       have r₂ := eq37974 x x y
       grind)
    | exact resolve eq55782 eq37974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37974 eq55782
  have eq56252 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1071 x X0
       have i₂ := eq55990 x
       grind)
    | exact superpose eq55990 eq1071
    | exact resolve eq1071 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq56314 : ∀ X1 : G, (σ x) = (τ (τ (k X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq14216 X1 x
       have i₂ := eq55990 x
       grind)
    | exact superpose eq55990 eq14216
    | exact resolve eq14216 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14216
  have eq56330 : ∀ X1 : G, (σ x) = (τ (k X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq14360 x X1
       have i₂ := eq55990 x
       grind)
    | exact superpose eq55990 eq14360
    | exact resolve eq14360 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14360
  have eq56478 : (σ x) = (τ (σ x)) := by
    first
    | (have i₁ := eq56314 x
       have i₂ := eq56330 x
       grind)
    | exact superpose eq56330 eq56314
    | exact resolve eq56314 eq56330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56314 eq56330
  have eq56521 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq56252 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq56252
    | exact resolve eq56252 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56252
  have eq56566 : x = (σ x) := by
    first
    | (have i₁ := eq56478
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq56478
    | exact resolve eq56478 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56478
  have eq57545 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq14
    | exact resolve eq14 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57547 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq13
    | exact resolve eq13 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59980 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq56521 x
       grind)
    | exact superpose eq56521 eq8
    | exact resolve eq8 eq56521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60102 : ∀ X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ x = (M.op X1 x) := by
    intro X1 X2
    first
    | (have i₁ := eq62 x x x x
       have i₂ := eq56521 x
       grind)
    | exact superpose eq56521 eq62
    | (have j0 := eq62 X1 X1 X2 X2
       grind)
    | exact resolve eq62 eq56521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq56521
  have eq99184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9774 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9774
  have eq99185 : ∀ X0 X1 : G, (σ x) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99184 X0 X1
       have i₂ := eq55990 (σ X0)
       grind)
    | exact superpose eq55990 eq99184
    | (have j0 := eq99184 X0 X1
       grind)
    | exact resolve eq99184 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55990 eq99184
  have eq99279 : ∀ X0 X1 : G, x ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99185 X0 X1
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq99185
    | (have j0 := eq99185 X0 X1
       grind)
    | exact resolve eq99185 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99185
  have eq530757 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq99279 x x
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq99279
    | exact resolve eq99279 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56566 eq99279
  have eq530788 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq530757 X0
       have j1 := eq60102 X0 x
       grind)
    | (have r₁ := eq530757 x
       have r₂ := eq60102 x x
       grind)
    | exact resolve eq530757 eq60102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60102 eq530757
  have eq530918 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq57547 X0
       have i₂ := eq530788 (σ X0)
       grind)
    | exact superpose eq530788 eq57547
    | exact resolve eq57547 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531338 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq530918 X0
       have i₂ := eq530788 X0
       grind)
    | exact superpose eq530788 eq530918
    | exact resolve eq530918 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530918
  have eq531457 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X1 X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq531338 (M.op X1 X0)
       have i₂ := eq59980 X0 X1
       grind)
    | exact superpose eq59980 eq531338
    | exact resolve eq531338 eq59980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531668 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (σ (k x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq57547 (M.op X0 x)
       have i₂ := eq531338 X0
       grind)
    | exact superpose eq531338 eq57547
    | exact resolve eq57547 eq531338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57547
  have eq531686 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (σ (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq531668 X0
       have i₂ := eq530788 (M.op X0 x)
       grind)
    | exact superpose eq530788 eq531668
    | exact resolve eq531668 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531668
  have eq531868 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (M.op (σ (M.op X0 x)) x) := by
    intro X0
    first
    | (have i₁ := eq531686 X0
       have i₂ := eq531338 (M.op X0 x)
       grind)
    | exact superpose eq531338 eq531686
    | exact resolve eq531686 eq531338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531338 eq531686
  have eq531989 : ∀ X0 : G, (σ (M.op x X0)) = (k x (M.op (σ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq531868 X0
       have i₂ := eq531457 x X0
       grind)
    | exact superpose eq531457 eq531868
    | exact resolve eq531868 eq531457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531457 eq531868
  have eq532078 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq531989 X0
       have i₂ := eq530788 (M.op (σ X0) x)
       grind)
    | exact superpose eq530788 eq531989
    | exact resolve eq531989 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530788 eq531989
  have eq532145 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq532078 X0
       have i₂ := eq59980 x (σ X0)
       grind)
    | exact superpose eq59980 eq532078
    | exact resolve eq532078 eq59980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59980 eq532078
  have eq533480 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq57545
       have i₂ := eq532145 y
       grind)
    | exact superpose eq532145 eq57545
    | (have r₁ := eq57545
       have r₂ := eq532145 y
       grind)
    | exact resolve eq57545 eq532145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57545 eq532145
  have eq533649 : False := by grind
  exact eq533649

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation3756 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3756 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X1 X0) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (τ X0) X1) X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
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
  clear eq16
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq20 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X2 X1 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq21 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq21 X1 X1 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq97 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    grind
  have eq311 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (M.op X1 X1)
       have i₂ := eq97 X1 (σ X0)
       grind)
    | exact superpose eq97 eq43
    | exact resolve eq43 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq311 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq311
    | exact resolve eq311 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq348 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq69 (σ X0) X1
       grind)
    | (have i₁ := eq35 X0 X0
       have i₂ := eq69 X0 (σ X0)
       grind)
    | exact superpose eq69 eq35
    | exact resolve eq35 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X1 (σ X2)
       have i₂ := eq35 X0 X2
       grind)
    | exact superpose eq35 eq69
    | (have j1 := eq35 X0 X2
       grind)
    | exact resolve eq69 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq441 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (τ (M.op X1 X1))
       have i₂ := eq332 (σ X0) X1
       grind)
    | exact superpose eq332 eq43
    | exact resolve eq43 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq444 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq441
    | exact resolve eq441 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq484 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (τ (τ (M.op X1 X1)))
       have i₂ := eq444 (σ X0) X1
       grind)
    | exact superpose eq444 eq43
    | exact resolve eq43 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq487 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq484
    | exact resolve eq484 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq742 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (k (k (τ (σ X0)) X0) X1)) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (σ X0) X0 X1
       have i₂ := eq47 (σ X0) X2
       grind)
    | exact superpose eq47 eq25
    | (have j1 := eq47 (σ X0) X2
       grind)
    | exact resolve eq25 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq47
  have eq802 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (k (k X0 X0) X1)) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq742 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq742
    | (have j0 := eq742 X0 X1 X2
       grind)
    | exact resolve eq742 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq809 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (k (k X0 X0) X1)) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq802 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq802
    | (have j0 := eq802 X0 X1 X2
       grind)
    | exact resolve eq802 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq1130 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq405 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq405
    | (have j0 := eq405 (M.op X0 X0)
       grind)
    | exact resolve eq405 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq1136 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1130 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1201 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1311 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1201 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1201
    | (have j0 := eq1201 X0 X1
       grind)
    | exact resolve eq1201 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq2946 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq444 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq444 eq348
    | (have j0 := eq348 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq348 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq2947 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (τ (M.op X0 X0))))) ∨ (M.op X1 X1) = (σ (τ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X1 (τ (τ (τ (M.op X0 X0))))
       have i₂ := eq487 (τ (τ (τ (M.op X0 X0)))) X0
       grind)
    | exact superpose eq487 eq348
    | (have j0 := eq348 X1 (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact resolve eq348 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq2952 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X1 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq348
    | (have j0 := eq348 X1 (M.op X0 X0)
       grind)
    | exact resolve eq348 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3011 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq348 X0 (τ X1)
       grind)
    | exact superpose eq348 eq17
    | (have j1 := eq348 X0 (τ X1)
       grind)
    | exact resolve eq17 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq3039 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2952 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952
  have eq3044 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq2947 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947
  have eq3045 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq2946 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946
  have eq3065 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3011 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3011
    | (have j0 := eq3011 X0 X1
       grind)
    | exact resolve eq3011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3089 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3044 X0 X1
       have i₂ := eq10 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq10 eq3044
    | exact resolve eq3044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044
  have eq3090 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3045 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq3045
    | exact resolve eq3045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq3092 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3065 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3065
    | (have j0 := eq3065 X0 X1
       grind)
    | exact resolve eq3065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065
  have eq15851 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X1 X2
       have i₂ := eq3092 X2 X0
       grind)
    | exact superpose eq3092 eq69
    | (have j1 := eq3092 X1 X0
       grind)
    | exact resolve eq69 eq3092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3092
  have eq18860 : ∀ X0 X1 X3 : G, (k X1 X0) = X1 ∨ (M.op X3 X3) = (k X0 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq97 x X1
       have i₂ := eq15851 X0 X3 x
       grind)
    | (have i₁ := eq97 X0 X1
       have i₂ := eq15851 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq15851 eq97
    | (have j1 := eq15851 X0 X3 x
       grind)
    | exact resolve eq97 eq15851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq21783 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq18860 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18860
  have eq21793 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq21783 X0 X1
       have j1 := eq15851 X0 X1 x
       grind)
    | (have r₁ := eq21783 (k X0 X0) X1
       have r₂ := eq15851 X0 X1 x
       grind)
    | (have r₁ := eq21783 X0 x
       have r₂ := eq15851 X0 X1 x
       grind)
    | (have r₁ := eq21783 (M.op x x) X1
       have r₂ := eq15851 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq21783 eq15851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15851 eq21783
  have eq22903 : ∀ X0 X2 : G, (k X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq3039 X2 x
       have i₂ := eq21793 X0 x
       grind)
    | exact superpose eq21793 eq3039
    | exact resolve eq3039 eq21793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22914 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3089 x X1
       have i₂ := eq21793 X0 x
       grind)
    | exact superpose eq21793 eq3089
    | exact resolve eq3089 eq21793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq23111 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X1
       have i₂ := eq21793 (τ X1) X0
       grind)
    | exact superpose eq21793 eq52
    | exact resolve eq52 eq21793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq21793
  have eq37231 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3039 X2 X1
       have i₂ := eq1311 X0 X2
       grind)
    | (have i₁ := eq3039 X0 X1
       have i₂ := eq1311 (M.op X0 X0) X1
       grind)
    | exact superpose eq1311 eq3039
    | (have j1 := eq1311 X0 X2
       grind)
    | exact resolve eq3039 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311 eq3039
  have eq60053 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq398 x X0 y
       grind)
    | exact superpose eq398 eq14
    | (have j1 := eq398 x X0 x
       grind)
    | exact resolve eq14 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq60268 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq60053 X0
       have j1 := eq37231 x X0 x
       grind)
    | (have r₁ := eq60053 X0
       have r₂ := eq37231 x x y
       grind)
    | exact resolve eq60053 eq37231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37231 eq60053
  have eq60540 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3090 x X0
       have i₂ := eq60268 x
       grind)
    | exact superpose eq60268 eq3090
    | exact resolve eq3090 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3090
  have eq60584 : ∀ X0 : G, (k X0 X0) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq22903 X0 x
       have i₂ := eq60268 x
       grind)
    | exact superpose eq60268 eq22903
    | exact resolve eq22903 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22903
  have eq60589 : ∀ X1 : G, (σ x) = (τ (τ (k X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq22914 X1 x
       have i₂ := eq60268 x
       grind)
    | exact superpose eq60268 eq22914
    | exact resolve eq22914 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22914
  have eq60601 : ∀ X1 : G, (σ x) = (τ (k X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq23111 x X1
       have i₂ := eq60268 x
       grind)
    | exact superpose eq60268 eq23111
    | exact resolve eq23111 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23111
  have eq60687 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1136 X0
       have i₂ := eq60268 (σ (M.op X0 X0))
       grind)
    | exact superpose eq60268 eq1136
    | exact resolve eq1136 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq60710 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq60687 x
       have i₂ := eq60268 x
       grind)
    | exact superpose eq60268 eq60687
    | exact resolve eq60687 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60268 eq60687
  have eq60747 : (σ x) = (τ (σ x)) := by
    first
    | (have i₁ := eq60589 x
       have i₂ := eq60601 x
       grind)
    | exact superpose eq60601 eq60589
    | exact resolve eq60589 eq60601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60589 eq60601
  have eq60779 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq60540 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq60540
    | exact resolve eq60540 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60540
  have eq60836 : x = (σ x) := by
    first
    | (have i₁ := eq60747
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq60747
    | exact resolve eq60747 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60747
  have eq61750 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq60836
       grind)
    | exact superpose eq60836 eq14
    | exact resolve eq14 eq60836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61752 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq60836
       grind)
    | exact superpose eq60836 eq13
    | exact resolve eq13 eq60836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65398 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq60779 x
       grind)
    | exact superpose eq60779 eq8
    | exact resolve eq8 eq60779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65526 : ∀ X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ x = (M.op X1 x) := by
    intro X1 X2
    first
    | (have i₁ := eq63 x x x x
       have i₂ := eq60779 x
       grind)
    | exact superpose eq60779 eq63
    | (have j0 := eq63 X1 X1 X2 X2
       grind)
    | exact resolve eq63 eq60779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq60779
  have eq216782 : ∀ X0 X1 X2 : G, (τ (σ (k X0 X1))) = (k (k X0 X0) X1) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (k (k X0 X0) X1)
       have i₂ := eq809 X0 X1 X2
       grind)
    | exact superpose eq809 eq9
    | (have j1 := eq809 X0 X1 X2
       grind)
    | exact resolve eq9 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq216785 : ∀ X0 X1 X2 : G, (τ (σ (k X0 X1))) = (k (σ (σ x)) X1) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216782 X0 X1 X2
       have i₂ := eq60584 X0
       grind)
    | exact superpose eq60584 eq216782
    | (have j0 := eq216782 X0 X1 X2
       grind)
    | exact resolve eq216782 eq60584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216782
  have eq216826 : ∀ X0 X1 X2 : G, (τ (σ (k X0 X1))) = (k (σ x) X1) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216785 X0 X1 X2
       have i₂ := eq60710
       grind)
    | exact superpose eq60710 eq216785
    | (have j0 := eq216785 X0 X1 X2
       grind)
    | exact resolve eq216785 eq60710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216785
  have eq216838 : ∀ X0 X1 X2 : G, (τ (σ (k X0 X1))) = (k x X1) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216826 X0 X1 X2
       have i₂ := eq60836
       grind)
    | exact superpose eq60836 eq216826
    | (have j0 := eq216826 X0 X1 X2
       grind)
    | exact resolve eq216826 eq60836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216826
  have eq216843 : ∀ X0 X1 X2 : G, (k X0 X1) = (k x X1) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216838 X0 X1 X2
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq216838
    | (have j0 := eq216838 X0 X1 X2
       grind)
    | exact resolve eq216838 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216838
  have eq1236483 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k (τ X0) X2) = (k x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216843 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq216843
    | (have j0 := eq216843 (τ X0) X2 X2
       grind)
    | exact resolve eq216843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216843
  have eq1237145 : ∀ X0 X1 X2 : G, (k (σ (τ X1)) X0) = (σ (k x (τ X0))) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq1236483 X1 X2 (τ X0)
       grind)
    | exact superpose eq1236483 eq17
    | (have j1 := eq1236483 X1 X2 X2
       grind)
    | exact resolve eq17 eq1236483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236483
  have eq1237174 : ∀ X0 X1 X2 : G, (k (σ (τ X1)) X0) = (k (σ x) X0) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1237145 X0 X1 X2
       have i₂ := eq17 X0 x
       grind)
    | exact superpose eq17 eq1237145
    | (have j0 := eq1237145 X0 X1 X2
       grind)
    | exact resolve eq1237145 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1237145
  have eq1237325 : ∀ X0 X1 X2 : G, (k (σ (τ X1)) X0) = (k x X0) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1237174 X0 X1 X2
       have i₂ := eq60836
       grind)
    | exact superpose eq60836 eq1237174
    | (have j0 := eq1237174 X0 X1 X2
       grind)
    | exact resolve eq1237174 eq60836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237174
  have eq1237426 : ∀ X0 X1 X2 : G, (k X1 X0) = (k x X0) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1237325 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1237325
    | (have j0 := eq1237325 X0 X1 X2
       grind)
    | exact resolve eq1237325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237325
  have eq1238128 : ∀ X0 : G, (k X0 X0) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1237426 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237426
  have eq1238131 : ∀ X0 : G, (σ (σ x)) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1238128 X0
       have i₂ := eq60584 X0
       grind)
    | exact superpose eq60584 eq1238128
    | (have j0 := eq1238128 X0
       grind)
    | exact resolve eq1238128 eq60584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60584 eq1238128
  have eq1238516 : ∀ X0 : G, (σ x) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1238131 X0
       have i₂ := eq60710
       grind)
    | exact superpose eq60710 eq1238131
    | (have j0 := eq1238131 X0
       grind)
    | exact resolve eq1238131 eq60710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60710 eq1238131
  have eq1238680 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1238516 X0
       have i₂ := eq60836
       grind)
    | exact superpose eq60836 eq1238516
    | (have j0 := eq1238516 X0
       grind)
    | exact resolve eq1238516 eq60836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60836 eq1238516
  have eq1238802 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1238680 X0
       have j1 := eq65526 X0 x
       grind)
    | (have r₁ := eq1238680 x
       have r₂ := eq65526 x x
       grind)
    | exact resolve eq1238680 eq65526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65526 eq1238680
  have eq1239276 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq61752 X0
       have i₂ := eq1238802 (σ X0)
       grind)
    | exact superpose eq1238802 eq61752
    | exact resolve eq61752 eq1238802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1240159 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1239276 X0
       have i₂ := eq1238802 X0
       grind)
    | exact superpose eq1238802 eq1239276
    | exact resolve eq1239276 eq1238802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239276
  have eq1241062 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X1 X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq1240159 (M.op X1 X0)
       have i₂ := eq65398 X0 X1
       grind)
    | exact superpose eq65398 eq1240159
    | exact resolve eq1240159 eq65398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1241486 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (σ (k x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq61752 (M.op X0 x)
       have i₂ := eq1240159 X0
       grind)
    | exact superpose eq1240159 eq61752
    | exact resolve eq61752 eq1240159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61752
  have eq1241508 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (σ (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq1241486 X0
       have i₂ := eq1238802 (M.op X0 x)
       grind)
    | exact superpose eq1238802 eq1241486
    | exact resolve eq1241486 eq1238802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241486
  have eq1241838 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (M.op (σ (M.op X0 x)) x) := by
    intro X0
    first
    | (have i₁ := eq1241508 X0
       have i₂ := eq1240159 (M.op X0 x)
       grind)
    | exact superpose eq1240159 eq1241508
    | exact resolve eq1241508 eq1240159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240159 eq1241508
  have eq1242035 : ∀ X0 : G, (σ (M.op x X0)) = (k x (M.op (σ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq1241838 X0
       have i₂ := eq1241062 x X0
       grind)
    | exact superpose eq1241062 eq1241838
    | exact resolve eq1241838 eq1241062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241062 eq1241838
  have eq1242161 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq1242035 X0
       have i₂ := eq1238802 (M.op (σ X0) x)
       grind)
    | exact superpose eq1238802 eq1242035
    | exact resolve eq1242035 eq1238802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238802 eq1242035
  have eq1242248 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1242161 X0
       have i₂ := eq65398 x (σ X0)
       grind)
    | exact superpose eq65398 eq1242161
    | exact resolve eq1242161 eq65398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65398 eq1242161
  have eq1246832 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq61750
       have i₂ := eq1242248 y
       grind)
    | exact superpose eq1242248 eq61750
    | (have r₁ := eq61750
       have r₂ := eq1242248 y
       grind)
    | exact resolve eq61750 eq1242248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61750 eq1242248
  have eq1247088 : False := by grind
  exact eq1247088
