import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyy_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq94 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq95 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq103 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq104 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq94
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq118
    | exact resolve eq118 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq120
    | exact resolve eq120 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq128 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq147 eq16
    | exact resolve eq16 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq175 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq149 eq16
    | exact resolve eq16 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq82 (τ X0)
       grind)
    | exact superpose eq82 eq35
    | (have j1 := eq82 (τ X0)
       grind)
    | exact resolve eq35 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq82
  have eq310 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq300
    | (have j0 := eq300 X0
       grind)
    | exact resolve eq300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq836 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ x) X0 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq4472 : (σ y) = (k (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq310
    | exact resolve eq310 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq310
  have eq4522 : (σ y) = (σ (k y (M.op y y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq37 eq4472
    | exact resolve eq4472 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4472
  have eq5299 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq103
    | (have j0 := eq103 x
       grind)
    | exact resolve eq103 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq5329 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5299
  have eq5334 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5329
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5329
    | exact resolve eq5329 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5329
  have eq5351 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5334
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5334 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5334
  have eq5359 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5351 eq50
    | exact resolve eq50 eq5351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq5351
  have eq5504 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq104
    | (have j0 := eq104 y
       grind)
    | exact resolve eq104 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq5533 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5504
  have eq5537 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5533
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq5533
    | exact resolve eq5533 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq5533
  have eq5561 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5537
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5537 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5537
  have eq5584 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5561 eq128
    | exact resolve eq128 eq5561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq5561
  have eq5879 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq150
    | (have j0 := eq150 (M.op x y)
       grind)
    | exact resolve eq150 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq5907 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5879
  have eq5910 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq149 eq5907
    | exact resolve eq5907 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq5907
  have eq5941 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5910
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5910 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5910
  have eq5981 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5941 eq175
    | exact resolve eq175 eq5941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq5941
  have eq17686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq17694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17686
    | exact resolve eq17686 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17686
  have eq17705 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17694
       have r₂ := eq28
       grind)
    | exact resolve eq17694 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17694
  have eq17707 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17705
    | exact resolve eq17705 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17705
  have eq17711 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17707 eq5584
    | exact resolve eq5584 eq17707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5584 eq17707
  have eq17770 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq17711
    | exact resolve eq17711 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17711
  have eq18006 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq17770
       grind)
    | exact superpose eq17770 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq17770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18020 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18006
  have eq18206 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq18020
       grind)
    | exact superpose eq18020 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq18020
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18020
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18020
       grind)
    | exact resolve eq13 eq18020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18250 : x ≠ y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18020
  have eq18252 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18206
  have eq18564 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17770
       have i₂ := eq18252
       grind)
    | exact superpose eq18252 eq17770
    | exact resolve eq17770 eq18252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17770 eq18252
  have eq18589 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq18564
  have eq18601 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18589
       have r₂ := eq18250
       grind)
    | exact resolve eq18589 eq18250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18250 eq18589
  have eq18635 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55 y y
       have i₂ := eq18601
       grind)
    | exact superpose eq18601 eq55
    | exact resolve eq55 eq18601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18677 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18635
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18635
    | exact resolve eq18635 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18635
  have eq18681 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18677 eq57
    | exact resolve eq57 eq18677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18677
  have eq18942 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18681 eq5359
    | exact resolve eq5359 eq18681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5359 eq18681
  have eq19018 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq18942
    | exact resolve eq18942 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18942
  have eq20034 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq19018
       grind)
    | exact superpose eq19018 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq19018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19018
  have eq20051 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20034
  have eq20091 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq836 x
       have i₂ := eq20051
       grind)
    | exact superpose eq20051 eq836
    | exact resolve eq836 eq20051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20051
  have eq20156 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56 eq20091
    | exact resolve eq20091 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20091
  have eq20163 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20156
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20156
    | exact resolve eq20156 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20156
  have eq20164 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq20163
  have eq20168 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20164 eq21
    | exact resolve eq21 eq20164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20243 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq20164
  have eq20297 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20168
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20168
    | exact resolve eq20168 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20168
  have eq20338 : ∀ X0 : G, (σ (k y X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20297 eq37
    | exact resolve eq37 eq20297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq20488 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38 eq20338
    | exact resolve eq20338 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq20338
  have eq31296 : (σ y) = (σ (k y x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4522
       have i₂ := eq18601
       grind)
    | exact superpose eq18601 eq4522
    | exact resolve eq4522 eq18601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4522 eq18601
  have eq31376 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31296
       have r₂ := eq20243
       grind)
    | exact resolve eq31296 eq20243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20243 eq31296
  have eq31384 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31376
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq31376
    | exact resolve eq31376 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31376
  have eq31385 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20297 eq31384
    | exact resolve eq31384 eq20297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31384
  have eq31424 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31385
  have eq31725 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31424 eq158
    | exact resolve eq158 eq31424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq31424
  have eq31749 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq31725
    | exact resolve eq31725 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq31725
  have eq31863 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31749 eq20488
    | exact resolve eq20488 eq31749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20488 eq31749
  have eq31874 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31863
  have eq31888 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31874
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq31874
    | exact resolve eq31874 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq31874
  have eq31904 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq31888
    | exact resolve eq31888 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31888
  have eq32044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31904 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq31904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31904
  have eq32063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq32044
    | exact resolve eq32044 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32044
  have eq32076 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32063
       have r₂ := eq28
       grind)
    | exact resolve eq32063 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32063
  have eq32079 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq32076
    | exact resolve eq32076 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32076
  have eq32080 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32079
  have eq32104 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32080 eq55
    | exact resolve eq55 eq32080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq32080
  have eq32156 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq32104
    | exact resolve eq32104 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32104
  have eq32166 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32156 eq28
    | exact resolve eq28 eq32156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32156
  have eq32208 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq32166
       have r₂ := eq20297
       grind)
    | exact resolve eq32166 eq20297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32166
  have eq32214 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32208 eq57
    | exact resolve eq57 eq32208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32208
  have eq32289 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32214 eq840
    | exact resolve eq840 eq32214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq32214
  have eq32367 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57 eq32289
    | exact resolve eq32289 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq32289
  have eq32382 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq32367
    | exact resolve eq32367 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32367
  have eq32386 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32382 eq28
    | exact resolve eq28 eq32382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32382
  have eq32429 : x = (M.op x y) := by
    first
    | (have r₁ := eq32386
       have r₂ := eq20297
       grind)
    | exact resolve eq32386 eq20297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20297 eq32386
  have eq32432 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq32429 eq21
    | exact resolve eq21 eq32429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq32435 : x = (M.op x x) := by
    first
    | exact superpose eq32429 eq56
    | exact resolve eq56 eq32429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32599 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq32432
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32432
    | exact resolve eq32432 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32432
  have eq32638 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq32599 eq27
    | exact resolve eq27 eq32599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32828 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq836 x
       have i₂ := eq32435
       grind)
    | exact superpose eq32435 eq836
    | exact resolve eq836 eq32435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq32834 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq32435
       grind)
    | exact superpose eq32435 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq32435
       grind)
    | exact resolve eq13 eq32435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32435
  have eq32883 : x = (k x x) := by grind
  clear eq32834
  have eq32904 : y = (M.op x y) := by
    first
    | exact superpose eq56 eq32828
    | exact resolve eq32828 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq32828
  have eq32911 : y = (M.op x y) := by
    first
    | (have i₁ := eq32904
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32904
    | exact resolve eq32904 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq32904
  have eq32915 : x = y := by
    first
    | exact superpose eq32429 eq32911
    | exact resolve eq32911 eq32429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32911
  have eq32918 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq32915
       grind)
    | exact superpose eq32915 eq25
    | exact resolve eq25 eq32915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32915
  have eq33095 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq32918
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32918
    | exact resolve eq32918 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32918
  have eq33154 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32599 eq33095
    | exact resolve eq33095 eq32599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33095
  have eq33811 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33154 eq32638
    | exact resolve eq32638 eq33154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32638 eq33154
  have eq35409 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq33811 eq5981
    | exact resolve eq5981 eq33811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5981 eq33811
  have eq35486 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32429 eq35409
    | exact resolve eq35409 eq32429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32429 eq35409
  have eq35504 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq35486
       have i₂ := eq32883
       grind)
    | exact superpose eq32883 eq35486
    | exact resolve eq35486 eq32883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32883 eq35486
  have eq35543 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35504 eq15
    | exact resolve eq15 eq35504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35504
  have eq35621 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35543
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35543
    | exact resolve eq35543 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq35543
  have eq35651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32599 eq35621
    | exact resolve eq35621 eq32599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32599 eq35621
  have eq35670 : False := by grind
  exact eq35670

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  clear eq44
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq82 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq93 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq50
    | exact resolve eq50 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq94 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq93
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq93
    | exact resolve eq93 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq93
  have eq118 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq118
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq118 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq133 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq127
    | exact resolve eq127 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq134 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq133
    | exact resolve eq133 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq135 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq134
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq134
    | exact resolve eq134 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq1070 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ x) X0 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq135 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq1188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1187
    | exact resolve eq1187 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1191 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1188
       have r₂ := eq28
       grind)
    | exact resolve eq1188 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1193 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1191
    | exact resolve eq1191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1219 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1193 eq57
    | exact resolve eq57 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1283 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1219 eq1074
    | exact resolve eq1074 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq1219
  have eq1305 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq57 eq1283
    | exact resolve eq1283 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1283
  have eq1309 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1305
    | exact resolve eq1305 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1323 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1309 eq1193
    | exact resolve eq1193 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq1309
  have eq1324 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1323
  have eq1328 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1324 eq30
    | exact resolve eq30 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1324
  have eq1349 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1328
    | exact resolve eq1328 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1328
  have eq1350 : x = (M.op x y) ∨ x = y := by grind
  clear eq1349
  have eq1385 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1350 eq56
    | exact resolve eq56 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : y = (M.op (M.op (M.op x y) x) y) ∨ x = y := by
    first
    | (have i₁ := eq1070 x
       have i₂ := eq1385
       grind)
    | exact superpose eq1385 eq1070
    | exact resolve eq1070 eq1385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq1385
  have eq1479 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56 eq1457
    | exact resolve eq1457 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1457
  have eq1483 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1479
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1479
    | exact resolve eq1479 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1566 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1483 eq1350
    | exact resolve eq1350 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq1483
  have eq1567 : x = y := by grind
  clear eq1566
  have eq1583 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1567
       grind)
    | exact superpose eq1567 eq19
    | exact resolve eq19 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1584 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1567
       grind)
    | exact superpose eq1567 eq25
    | exact resolve eq25 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1567
  have eq1604 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1584
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1584
    | exact resolve eq1584 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1584
  have eq1687 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1604 eq27
    | exact resolve eq27 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1604
  have eq1742 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1687 eq94
    | exact resolve eq94 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1687
  have eq1762 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1742
       have i₂ := eq1583
       grind)
    | exact superpose eq1583 eq1742
    | exact resolve eq1742 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583 eq1742
  have eq1767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1762 eq15
    | exact resolve eq15 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq1794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1767
    | exact resolve eq1767 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1767
  have eq1799 : False := by grind
  exact eq1799

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyy_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X0 X1) X0
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq35
    | exact resolve eq35 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq52 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq73 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq178 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq73 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq73 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq73 X1 X1
       grind)
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq187 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq189 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq187
    | (have j0 := eq187 X0 X1
       grind)
    | exact resolve eq187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq193 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       have j1 := eq185 X1 X0
       grind)
    | (have r₁ := eq189 X1 X0
       have r₂ := eq185 X0 X1
       grind)
    | (have r₁ := eq189 (k X1 X0) X1
       have r₂ := eq185 X0 X1
       grind)
    | (have r₁ := eq189 X1 X1
       have r₂ := eq185 X1 X1
       grind)
    | exact resolve eq189 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq189
  have eq648 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq193
    | exact resolve eq193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq193 y x
       grind)
    | exact superpose eq193 eq16
    | (have j1 := eq193 y x
       grind)
    | exact resolve eq16 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq682 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq648 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq648
    | (have j0 := eq648 X0 X1
       grind)
    | exact resolve eq648 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq648
  have eq952 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq682 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq682
    | exact resolve eq682 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq1129 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq952 (τ X1) X0
       grind)
    | exact superpose eq952 eq18
    | (have j1 := eq952 (τ X1) X0
       grind)
    | exact resolve eq18 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1407 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1129 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1129
    | exact resolve eq1129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1479 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1407 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1407
    | (have j0 := eq1407 X0 X1
       grind)
    | exact resolve eq1407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq2003 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq660
       have i₂ := eq1479 y x
       grind)
    | exact superpose eq1479 eq660
    | (have j1 := eq1479 (σ y) (σ x)
       grind)
    | (have r₁ := eq660
       have r₂ := eq1479 y x
       grind)
    | exact resolve eq660 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq2004 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2003
  have eq2069 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  have eq2076 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x x
       have i₂ := eq2004
       grind)
    | exact superpose eq2004 eq37
    | exact resolve eq37 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq2099 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq660
       have i₂ := eq2069
       grind)
    | exact superpose eq2069 eq660
    | exact resolve eq660 eq2069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq2069
  have eq2104 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2099
  have eq2260 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2104
       have i₂ := eq2076
       grind)
    | exact superpose eq2076 eq2104
    | exact resolve eq2104 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076 eq2104
  have eq2261 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2260
  have eq2262 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2261
  have eq2269 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | (have i₁ := eq52 x
       have i₂ := eq2262
       grind)
    | exact superpose eq2262 eq52
    | exact resolve eq52 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2287 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 (σ x) (σ x)
       have i₂ := eq2262
       grind)
    | exact superpose eq2262 eq37
    | exact resolve eq37 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq2311 : y = (k y x) := by
    first
    | (have i₁ := eq2269
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2269
    | exact resolve eq2269 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2388 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq952 y x
       have i₂ := eq2311
       grind)
    | exact superpose eq2311 eq952
    | (have j0 := eq952 y x
       grind)
    | exact resolve eq952 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq2311
  have eq2588 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2287
       grind)
    | exact superpose eq2287 eq16
    | exact resolve eq16 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2287
  have eq2800 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2588
       have i₂ := eq2388
       grind)
    | exact superpose eq2388 eq2588
    | exact resolve eq2588 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388
  have eq2828 : y = (M.op x x) := by grind
  clear eq2800
  have eq2839 : y = (M.op x y) := by
    first
    | (have i₁ := eq37 x x
       have i₂ := eq2828
       grind)
    | exact superpose eq2828 eq37
    | exact resolve eq37 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2828
  have eq2964 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2588
       have i₂ := eq2839
       grind)
    | exact superpose eq2839 eq2588
    | exact resolve eq2588 eq2839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2588 eq2839
  have eq2992 : False := by grind
  exact eq2992

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq43 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq72 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
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
  have eq86 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq98 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq56 eq94
    | exact resolve eq94 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq100 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq98
    | exact resolve eq98 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq101 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq62 eq100
    | exact resolve eq100 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq100
  have eq111 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq116 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq111
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq111
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq111 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq16
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq132 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq125
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq125
    | exact resolve eq125 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq133 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq132
    | exact resolve eq132 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq180 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq122
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq122 eq16
    | exact resolve eq16 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq188 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq180
  have eq393 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq63
    | (have j0 := eq63 y
       grind)
    | exact resolve eq63 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq626 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq55
    | (have j1 := eq88 X0 X1
       grind)
    | exact resolve eq55 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq88 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq631 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq630 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq955 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ x) X0 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq61 X1 X2 X0
       grind)
    | exact superpose eq61 eq55
    | exact resolve eq55 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4160 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq631 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq631
    | (have j0 := eq631 (τ X0)
       grind)
    | exact resolve eq631 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq631
  have eq4168 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4160 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4160
    | (have j0 := eq4160 X0
       grind)
    | exact resolve eq4160 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4160
  have eq4174 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4168 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4168
    | (have j0 := eq4168 X0
       grind)
    | exact resolve eq4168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168
  have eq5442 : x ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq56 eq72
    | (have j0 := eq72 x y
       grind)
    | exact resolve eq72 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq72
  have eq8319 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ x) X0) (σ (τ X0))) ∨ (σ x) = (M.op (σ x) (σ (τ X0))) ∨ (σ x) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq626 x (τ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq626
    | (have j0 := eq626 x (τ X0)
       grind)
    | exact resolve eq626 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq8349 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (M.op x y)) X0) (σ (τ X0))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (M.op x y)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq116 eq626
    | (have j0 := eq626 (M.op x y) (τ X0)
       grind)
    | exact resolve eq626 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq626
  have eq8512 : ∀ X0 : G, (M.op (k (σ (M.op x y)) X0) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (M.op x y)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8349 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8349
    | (have j0 := eq8349 X0
       grind)
    | exact resolve eq8349 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8349
  have eq8542 : ∀ X0 : G, (M.op (k (σ x) X0) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ (τ X0))) ∨ (σ x) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8319 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8319
    | (have j0 := eq8319 X0
       grind)
    | exact resolve eq8319 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8319
  have eq8602 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (M.op (k (σ (M.op x y)) X0) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8512 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8512
    | (have j0 := eq8512 X0
       grind)
    | exact resolve eq8512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8512
  have eq8632 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (k (σ x) X0) X0) = X0 ∨ (σ x) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8542 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8542
    | (have j0 := eq8542 X0
       grind)
    | exact resolve eq8542 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8542
  have eq8688 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (M.op (k (σ (M.op x y)) X0) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq21 eq8602
    | (have j0 := eq8602 X0
       grind)
    | exact resolve eq8602 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8602
  have eq8716 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (k (σ x) X0) X0) = X0 ∨ (σ x) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8632 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8632
    | (have j0 := eq8632 X0
       grind)
    | exact resolve eq8632 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8632
  have eq8771 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (M.op (k (σ (M.op x y)) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8688 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8688
    | (have j0 := eq8688 X0
       grind)
    | exact resolve eq8688 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8688
  have eq8799 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (M.op (k (σ x) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8716 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8716
    | (have j0 := eq8716 X0
       grind)
    | exact resolve eq8716 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8716
  have eq8853 : ∀ X0 : G, (M.op (k (σ (M.op x y)) X0) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq21 eq8771
    | (have j0 := eq8771 X0
       grind)
    | exact resolve eq8771 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8771
  have eq8881 : ∀ X0 : G, (M.op (k (σ x) X0) X0) = X0 ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq8799 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8799
    | (have j0 := eq8799 X0
       grind)
    | exact resolve eq8799 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8799
  have eq14711 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq101 eq86
    | exact resolve eq86 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq14730 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq14711
    | exact resolve eq14711 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14711
  have eq24001 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq14730
       have r₂ := eq5442
       grind)
    | exact resolve eq14730 eq5442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5442 eq14730
  have eq26068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq133 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq26068
    | exact resolve eq26068 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26068
  have eq26086 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq26075
       have r₂ := eq28
       grind)
    | exact resolve eq26075 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26075
  have eq26092 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26086 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26086
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq26086
       grind)
    | exact resolve eq12 eq26086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26086
  have eq26141 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq26092
  have eq26142 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq26141
  have eq26604 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26142 eq131
    | exact resolve eq131 eq26142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq26142
  have eq26629 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq26604
    | exact resolve eq26604 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq26604
  have eq26632 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq26629
       have r₂ := eq12 y x
       grind)
    | exact resolve eq26629 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26629
  have eq26644 : (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26632 eq66
    | exact resolve eq66 eq26632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26632
  have eq27115 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26644 eq133
    | exact resolve eq133 eq26644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq26644
  have eq27134 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (k y x) := by grind
  clear eq27115
  have eq27149 : y = (k y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq27134
       have r₂ := eq12 y x
       grind)
    | exact resolve eq27134 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27134
  have eq27166 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq27149
       grind)
    | exact superpose eq27149 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq27149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27149
  have eq27173 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq27166
  have eq27180 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq27173
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27173
    | exact resolve eq27173 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27173
  have eq28297 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq61 y x X0
       have i₂ := eq27180
       grind)
    | exact superpose eq27180 eq61
    | exact resolve eq61 eq27180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq27180
  have eq28375 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq28297 X0
       have i₂ := eq55 y X0
       grind)
    | exact superpose eq55 eq28297
    | exact resolve eq28297 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28297
  have eq34468 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq59 x x
       have i₂ := eq28375 X0
       grind)
    | exact superpose eq28375 eq59
    | (have j1 := eq28375 X0
       grind)
    | exact resolve eq59 eq28375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq28375
  have eq34521 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq34468 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34468
    | (have j0 := eq34468 X0
       grind)
    | exact resolve eq34468 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34468
  have eq34522 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq34521 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34521
  have eq34549 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq55 y X0
       have i₂ := eq34522 X0
       grind)
    | exact superpose eq34522 eq55
    | exact resolve eq55 eq34522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34522
  have eq35101 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq34549 x
       grind)
    | exact superpose eq34549 eq19
    | (have j1 := eq34549 x
       grind)
    | exact resolve eq19 eq34549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34549
  have eq35165 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq35101
  have eq35175 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35165 eq29
    | exact resolve eq29 eq35165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq35190 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35165 eq86
    | exact resolve eq86 eq35165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq35165
  have eq35355 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq183 eq35190
    | exact resolve eq35190 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq35190
  have eq35366 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq35175
    | exact resolve eq35175 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq35175
  have eq35475 : x = (k x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35366 eq24001
    | exact resolve eq24001 eq35366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35477 : x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq35475
       have r₂ := eq73
       grind)
    | exact resolve eq35475 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq35475
  have eq38232 : (M.op x y) ≠ (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35355 eq4174
    | (have j0 := eq4174 (M.op x y)
       grind)
    | exact resolve eq4174 eq35355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4174 eq35355
  have eq38786 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq35477
       grind)
    | exact superpose eq35477 eq45
    | exact resolve eq45 eq35477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35477
  have eq38818 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38786
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38786
    | exact resolve eq38786 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38786
  have eq90527 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq24001 eq38232
    | exact resolve eq38232 eq24001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24001 eq38232
  have eq90534 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq90527
       have r₂ := eq35366
       grind)
    | exact resolve eq90527 eq35366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90527
  have eq98857 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq90534
  have eq98865 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq98857
       have r₂ := eq35366
       grind)
    | exact resolve eq98857 eq35366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35366 eq98857
  have eq98907 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98865 eq393
    | exact resolve eq393 eq98865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq98865
  have eq99031 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq98907
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98907
    | exact resolve eq98907 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq98907
  have eq99032 : y = (M.op x y) := by grind
  clear eq99031
  have eq99035 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq99032 eq21
    | exact resolve eq21 eq99032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq99073 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq99032 eq188
    | exact resolve eq188 eq99032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq99032
  have eq99340 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq99035
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq99035
    | exact resolve eq99035 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99035
  have eq99343 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq99340 eq27
    | exact resolve eq27 eq99340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq99408 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq99340 eq955
    | exact resolve eq955 eq99340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq99489 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq99340 eq38818
    | exact resolve eq38818 eq99340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38818
  have eq100637 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq99489 eq8881
    | (have j0 := eq8881 (σ (M.op x y))
       grind)
    | exact resolve eq8881 eq99489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8881 eq99489
  have eq100648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq99343 eq100637
    | exact resolve eq100637 eq99343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100637
  have eq100660 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq100648
       have r₂ := eq28
       grind)
    | exact resolve eq100648 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100648
  have eq100671 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq99343 eq100660
    | exact resolve eq100660 eq99343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100660
  have eq145632 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq100671 eq55
    | exact resolve eq55 eq100671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100671
  have eq145742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq99343 eq145632
    | exact resolve eq145632 eq99343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145632
  have eq145748 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq145742
       have r₂ := eq28
       grind)
    | exact resolve eq145742 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145742
  have eq145767 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99073
       have i₂ := eq145748
       grind)
    | exact superpose eq145748 eq99073
    | exact resolve eq99073 eq145748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99073
  have eq145783 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66 y
       have i₂ := eq145748
       grind)
    | exact superpose eq145748 eq66
    | exact resolve eq66 eq145748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq145748
  have eq145905 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq145767
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq145767
    | exact resolve eq145767 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145767
  have eq147193 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq145783
       grind)
    | exact superpose eq145783 eq45
    | exact resolve eq45 eq145783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq145783
  have eq147233 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99340 eq147193
    | exact resolve eq147193 eq99340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147193
  have eq147252 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq147233
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq147233
    | exact resolve eq147233 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147233
  have eq147267 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99340 eq147252
    | exact resolve eq147252 eq99340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147252
  have eq147566 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq145905 eq8853
    | (have j0 := eq8853 (σ (M.op x y))
       grind)
    | exact resolve eq8853 eq145905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8853 eq145905
  have eq147585 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq147566
  have eq147588 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99343 eq147585
    | exact resolve eq147585 eq99343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147585
  have eq147600 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq147588
       have r₂ := eq28
       grind)
    | exact resolve eq147588 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147588
  have eq148971 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) = (M.op X0 (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y)))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq147600 eq989
    | exact resolve eq989 eq147600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq147600
  have eq149022 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq148971 x
       have i₂ := eq55 sF1 x
       grind)
    | exact superpose eq55 eq148971
    | exact resolve eq148971 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq148971
  have eq150876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq149022 eq99343
    | exact resolve eq99343 eq149022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149022
  have eq150929 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq150876
       have r₂ := eq28
       grind)
    | exact resolve eq150876 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150876
  have eq150983 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq150929 eq57
    | exact resolve eq57 eq150929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150929
  have eq152283 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq150983 eq99408
    | exact resolve eq99408 eq150983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99408 eq150983
  have eq152419 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq57 eq152283
    | exact resolve eq152283 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq152283
  have eq152445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq99343 eq152419
    | exact resolve eq152419 eq99343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152419
  have eq152460 : x = y := by
    first
    | (have r₁ := eq152445
       have r₂ := eq28
       grind)
    | exact resolve eq152445 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152445
  have eq152473 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq152460
       grind)
    | exact superpose eq152460 eq25
    | exact resolve eq25 eq152460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq152460
  have eq152925 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq99340 eq152473
    | exact resolve eq152473 eq99340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99340 eq152473
  have eq153087 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq152925
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq152925
    | exact resolve eq152925 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq152925
  have eq153293 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq153087 eq99343
    | exact resolve eq99343 eq153087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99343
  have eq153313 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153087 eq147267
    | exact resolve eq147267 eq153087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147267 eq153087
  have eq153319 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq153313
       have r₂ := eq28
       grind)
    | exact resolve eq153313 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153313
  have eq156480 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq153319 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq153319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153319
  have eq156491 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq156480
  have eq156503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153293 eq156491
    | exact resolve eq156491 eq153293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153293 eq156491
  have eq156524 : False := by grind
  exact eq156524

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq81
  have eq105 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq105
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq16
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq181 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq498 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X0)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq49
    | (have j0 := eq49 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq49 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq802 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ x) X0 (σ y)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq57 X1 X2 X0
       grind)
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq5583 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq79
    | (have j0 := eq79 x
       grind)
    | exact resolve eq79 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq5612 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5583
  have eq5617 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5612
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5612
    | exact resolve eq5612 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5612
  have eq6487 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (k X0 x)) (σ x)) (σ x))) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq181 eq498
    | (have j1 := eq181 X0
       grind)
    | exact resolve eq498 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq498
  have eq25050 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25057 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25050
    | exact resolve eq25050 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25050
  have eq25068 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq25057
       have r₂ := eq28
       grind)
    | exact resolve eq25057 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25057
  have eq25074 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25068 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq25068
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq25068
       grind)
    | exact resolve eq12 eq25068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25123 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq25074
  have eq25124 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq25123
  have eq25578 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25124 eq55
    | exact resolve eq55 eq25124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25124
  have eq25623 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25578
    | exact resolve eq25578 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25578
  have eq25631 : (τ (σ x)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25623 eq115
    | exact resolve eq115 eq25623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq25623
  have eq25659 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq25631
    | exact resolve eq25631 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25631
  have eq25663 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq25659
       have r₂ := eq12 y x
       grind)
    | exact resolve eq25659 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25659
  have eq25955 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq25663
       grind)
    | exact superpose eq25663 eq83
    | exact resolve eq83 eq25663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq25966 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq25663
  have eq26019 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq25955
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25955
    | exact resolve eq25955 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25955
  have eq26394 : x ≠ y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq25966
  have eq28228 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq26019
       have r₂ := eq26394
       grind)
    | exact resolve eq26019 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26019 eq26394
  have eq28229 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5617 eq28228
    | exact resolve eq28228 eq5617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5617 eq28228
  have eq105239 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28229 eq55
    | exact resolve eq55 eq28229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28229
  have eq105335 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq105239
    | exact resolve eq105239 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105239
  have eq105336 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq105335
  have eq105854 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105336 eq802
    | exact resolve eq802 eq105336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq105336
  have eq106011 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53 eq105854
    | exact resolve eq105854 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105854
  have eq106022 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq106011
    | exact resolve eq106011 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106011
  have eq106023 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq106022
  have eq106037 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq106023
       grind)
    | exact superpose eq106023 eq105
    | exact resolve eq105 eq106023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106108 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106037
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq106037
    | exact resolve eq106037 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106037
  have eq106186 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106108
  have eq106223 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq106186
    | exact resolve eq106186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106186
  have eq132355 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq106223 eq834
    | exact resolve eq834 eq106223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106223
  have eq132440 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq132355 x
       have i₂ := eq51 sF3 x
       grind)
    | exact superpose eq51 eq132355
    | exact resolve eq132355 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132355
  have eq147508 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq132440 eq55
    | (have j1 := eq132440 (σ x)
       grind)
    | exact resolve eq55 eq132440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132440
  have eq147607 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq147508
    | (have j0 := eq147508 (σ x)
       grind)
    | exact resolve eq147508 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147508
  have eq147608 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq147607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147607
  have eq147896 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq147608 eq27
    | (have j1 := eq147608 (σ x)
       grind)
    | exact resolve eq27 eq147608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147608
  have eq147973 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq147896
  have eq148106 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq147973
  have eq525347 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ x)) (σ x))) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6487 y
       have i₂ := eq106023
       grind)
    | exact superpose eq106023 eq6487
    | (have j0 := eq6487 y
       grind)
    | exact resolve eq6487 eq106023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6487 eq106023
  have eq525818 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ x)) (σ x))) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq525347
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq525347
    | exact resolve eq525347 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525347
  have eq525872 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq525818
       have i₂ := eq51 sF2 sF2
       grind)
    | exact superpose eq51 eq525818
    | exact resolve eq525818 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525818
  have eq525898 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53 eq525872
    | exact resolve eq525872 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525872
  have eq525918 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq525898
    | exact resolve eq525898 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525898
  have eq525919 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq525918
  have eq525929 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq525919
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq525919
    | exact resolve eq525919 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525919
  have eq525932 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq525929
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq525929
    | exact resolve eq525929 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525929
  have eq526117 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq525932 eq834
    | exact resolve eq834 eq525932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq525932
  have eq526568 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq526117 x
       have i₂ := eq51 sF3 x
       grind)
    | exact superpose eq51 eq526117
    | exact resolve eq526117 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq526117
  have eq527197 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq526568 eq55
    | (have j1 := eq526568 (σ x)
       grind)
    | exact resolve eq55 eq526568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526568
  have eq527528 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq527197
    | (have j0 := eq527197 (σ x)
       grind)
    | exact resolve eq527197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527197
  have eq527529 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq527528 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527528
  have eq528430 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq527529 eq27
    | (have j1 := eq527529 (σ x)
       grind)
    | exact resolve eq27 eq527529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527529
  have eq528638 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq528430
  have eq528656 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq528638 eq28
    | exact resolve eq28 eq528638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq528658 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq528638 eq53
    | exact resolve eq53 eq528638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq530078 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25068 eq528658
    | exact resolve eq528658 eq25068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25068
  have eq1804027 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq530078
  have eq1811703 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1804027 eq117
    | exact resolve eq117 eq1804027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1804027
  have eq1811906 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq1811703
  have eq1811919 : y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1811906
       have r₂ := eq528656
       grind)
    | exact resolve eq1811906 eq528656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811906
  have eq1811987 : y ≠ y ∨ y = (M.op x x) ∨ x = (k y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1811919
       grind)
    | exact superpose eq1811919 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1811919
       grind)
    | exact resolve eq12 eq1811919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811919
  have eq1812654 : y ≠ y ∨ y = (M.op x x) ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq1811987
  have eq1812655 : y = (M.op x x) ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq1812654
  have eq1814419 : y = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55 x x
       have i₂ := eq1812655
       grind)
    | exact superpose eq1812655 eq55
    | exact resolve eq55 eq1812655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1812655
  have eq1815215 : x = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1814419
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1814419
    | exact resolve eq1814419 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814419
  have eq1815288 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq1815215
       grind)
    | exact superpose eq1815215 eq105
    | exact resolve eq105 eq1815215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq1815215
  have eq1815597 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1815288
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1815288
    | exact resolve eq1815288 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815288
  have eq1816420 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1815597 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1815597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1816557 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq1816420
    | exact resolve eq1816420 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1816420
  have eq1816585 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1816557
       have r₂ := eq148106
       grind)
    | exact resolve eq1816557 eq148106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148106 eq1816557
  have eq1816608 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq528638 eq1816585
    | exact resolve eq1816585 eq528638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528638 eq1816585
  have eq1816614 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq528658 eq1816608
    | exact resolve eq1816608 eq528658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816608
  have eq1816615 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1816614
  have eq1825927 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1816615
  have eq1826989 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1825927 eq1815597
    | exact resolve eq1815597 eq1825927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815597 eq1825927
  have eq1827056 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1826989
  have eq1827104 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1827056 eq30
    | exact resolve eq30 eq1827056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1827056
  have eq1828593 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1827104
    | exact resolve eq1827104 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827104
  have eq1828801 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1828593 eq21
    | exact resolve eq21 eq1828593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828593
  have eq1829615 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1828801
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1828801
    | exact resolve eq1828801 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828801
  have eq1829640 : x = y := by
    first
    | (have r₁ := eq1829615
       have r₂ := eq528656
       grind)
    | exact resolve eq1829615 eq528656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829615
  have eq1829643 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1829640
       grind)
    | exact superpose eq1829640 eq19
    | exact resolve eq19 eq1829640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1829644 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1829640
       grind)
    | exact superpose eq1829640 eq25
    | exact resolve eq25 eq1829640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1829640
  have eq1830429 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1829644
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1829644
    | exact resolve eq1829644 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829644
  have eq1831152 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1830429 eq528656
    | exact resolve eq528656 eq1830429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528656
  have eq1831154 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1830429 eq528658
    | exact resolve eq528658 eq1830429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528658 eq1830429
  have eq1837785 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq1831154
  have eq1854702 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq1837785 eq77
    | exact resolve eq77 eq1837785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1837785
  have eq1854955 : x = (k x x) := by
    first
    | exact superpose eq29 eq1854702
    | exact resolve eq1854702 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1854702
  have eq1943371 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq1854955
       grind)
    | exact superpose eq1854955 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq1854955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1854955
  have eq1943493 : x = (M.op x x) := by grind
  clear eq1943371
  have eq1943538 : x = (M.op x y) := by
    first
    | (have i₁ := eq1943493
       have i₂ := eq1829643
       grind)
    | exact superpose eq1829643 eq1943493
    | exact resolve eq1943493 eq1829643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829643 eq1943493
  have eq1943838 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1943538 eq21
    | exact resolve eq21 eq1943538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1943538
  have eq1944790 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1943838
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1943838
    | exact resolve eq1943838 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1943838
  have eq1944989 : False := by grind
  exact eq1944989

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  clear eq55
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq109 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq109
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq123
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq123
    | exact resolve eq123 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq131 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq130
    | exact resolve eq130 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq132 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq131
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq131
    | exact resolve eq131 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq625 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq88 X0 X0
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq633 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq625 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq635 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq633 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq633 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq633 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq633 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq644 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq635 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq635
    | (have j0 := eq635 X0 X1
       grind)
    | exact resolve eq635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq957 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq961 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ x) X0 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq15304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq132 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15304
    | exact resolve eq15304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15304
  have eq15322 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15311
       have r₂ := eq28
       grind)
    | exact resolve eq15311 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15311
  have eq15324 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15322
    | exact resolve eq15322 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15322
  have eq15329 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15324 eq66
    | exact resolve eq66 eq15324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15336 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15324 eq59
    | exact resolve eq59 eq15324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15324
  have eq15372 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15336
    | exact resolve eq15336 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15336
  have eq15379 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq15372
       grind)
    | exact superpose eq15372 eq66
    | exact resolve eq66 eq15372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15372
  have eq15657 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq629 x y
       have i₂ := eq15379
       grind)
    | exact superpose eq15379 eq629
    | (have j0 := eq629 x y
       grind)
    | exact resolve eq629 eq15379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15379
  have eq15660 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15657
  have eq15664 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15660
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15660
    | exact resolve eq15660 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15660
  have eq15677 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15664
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15664
    | exact resolve eq15664 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664
  have eq15683 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15677
    | exact resolve eq15677 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15677
  have eq15684 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15683
  have eq15690 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15684
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15684
    | exact resolve eq15684 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15684
  have eq15696 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15690
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15690
    | exact resolve eq15690 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15690
  have eq16805 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15696 eq59
    | exact resolve eq59 eq15696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15696
  have eq16843 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq16805
    | exact resolve eq16805 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16805
  have eq16844 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16843
  have eq16847 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16844 eq28
    | exact resolve eq28 eq16844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16844
  have eq17898 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15329 eq132
    | exact resolve eq132 eq15329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq15329
  have eq17916 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17898
  have eq18062 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59 x x
       have i₂ := eq17916
       grind)
    | exact superpose eq17916 eq59
    | exact resolve eq59 eq17916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq17916
  have eq18103 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18062
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18062
    | exact resolve eq18062 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18062
  have eq18111 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18103 eq57
    | exact resolve eq57 eq18103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18406 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18111 eq961
    | exact resolve eq961 eq18111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18111
  have eq18475 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57 eq18406
    | exact resolve eq18406 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18406
  have eq18482 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq18475
    | exact resolve eq18475 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18475
  have eq18638 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18482 eq18103
    | exact resolve eq18103 eq18482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18103 eq18482
  have eq18639 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18638
  have eq18671 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18639 eq30
    | exact resolve eq30 eq18639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18639
  have eq18823 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq18671
    | exact resolve eq18671 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18671
  have eq18825 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18823 eq29
    | exact resolve eq29 eq18823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18823
  have eq18981 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq18825
    | exact resolve eq18825 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq18825
  have eq18982 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18981
  have eq19102 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18982 eq21
    | exact resolve eq21 eq18982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18982
  have eq19229 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19102
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19102
    | exact resolve eq19102 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19102
  have eq19308 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq19229 eq16847
    | (have r₁ := eq16847
       have r₂ := eq19229
       grind)
    | exact resolve eq16847 eq19229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16847
  have eq19326 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19308
  have eq19327 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19326
  have eq19393 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19327 eq57
    | exact resolve eq57 eq19327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19327
  have eq19797 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19393 eq961
    | exact resolve eq961 eq19393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq19393
  have eq19867 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq57 eq19797
    | exact resolve eq19797 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq19797
  have eq19874 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq19867
    | exact resolve eq19867 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19867
  have eq19883 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19874 eq28
    | exact resolve eq28 eq19874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19874
  have eq19917 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq19883
       have r₂ := eq19229
       grind)
    | exact resolve eq19883 eq19229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19229 eq19883
  have eq19922 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq19917 eq56
    | exact resolve eq56 eq19917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20351 : y = (M.op (M.op (M.op x y) x) y) ∨ x = y := by
    first
    | (have i₁ := eq957 x
       have i₂ := eq19922
       grind)
    | exact superpose eq19922 eq957
    | exact resolve eq957 eq19922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq19922
  have eq20419 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56 eq20351
    | exact resolve eq20351 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq20351
  have eq20426 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq20419
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20419
    | exact resolve eq20419 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20419
  have eq20509 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq20426 eq19917
    | exact resolve eq19917 eq20426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19917 eq20426
  have eq20510 : x = y := by grind
  clear eq20509
  have eq20635 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20510
       grind)
    | exact superpose eq20510 eq19
    | exact resolve eq19 eq20510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20636 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20510
       grind)
    | exact superpose eq20510 eq25
    | exact resolve eq25 eq20510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20510
  have eq20752 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20636
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20636
    | exact resolve eq20636 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20636
  have eq20754 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20752 eq27
    | exact resolve eq27 eq20752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20752
  have eq20927 : x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq20635
       grind)
    | exact superpose eq20635 eq66
    | exact resolve eq66 eq20635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq20635
  have eq21084 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20927 eq629
    | (have j0 := eq629 x (M.op x y)
       grind)
    | exact resolve eq629 eq20927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq21085 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20927 eq644
    | (have j0 := eq644 (M.op x y) x
       grind)
    | exact resolve eq644 eq20927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq20927
  have eq21087 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq21085
  have eq21088 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq21084
  have eq21092 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq21087
    | exact resolve eq21087 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21087
  have eq21093 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq21088
    | exact resolve eq21088 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21088
  have eq21106 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21092
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21092
    | exact resolve eq21092 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21092
  have eq21107 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21093
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21093
    | exact resolve eq21093 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21093
  have eq21115 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21106
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21106
    | exact resolve eq21106 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21106
  have eq21116 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq21107
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21107
    | exact resolve eq21107 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21107
  have eq21124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20754 eq21115
    | exact resolve eq21115 eq20754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21115
  have eq21125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20754 eq21116
    | exact resolve eq21116 eq20754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21116
  have eq21131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq21124
    | exact resolve eq21124 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21124
  have eq21132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq21125
    | exact resolve eq21125 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq21125
  have eq21138 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq21131
       have r₂ := eq28
       grind)
    | exact resolve eq21131 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21131
  have eq21139 : (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq21132
       have r₂ := eq28
       grind)
    | exact resolve eq21132 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21132
  have eq21257 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21138 eq20754
    | exact resolve eq20754 eq21138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20754
  have eq21711 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21138 eq21139
    | exact resolve eq21139 eq21138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21138 eq21139
  have eq22017 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21711 eq21257
    | exact resolve eq21257 eq21711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21257 eq21711
  have eq22018 : False := by grind
  exact eq22018

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq104 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq104
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq661 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq62 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq62 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq62 X0 X0
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq667 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq661 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq669 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq667 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq667 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq667 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq667 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq679 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq799 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x X0 y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ x) X0 (σ y)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq11452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11452
    | exact resolve eq11452 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11452
  have eq11464 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11453
       have r₂ := eq28
       grind)
    | exact resolve eq11453 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11453
  have eq11466 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11464
    | exact resolve eq11464 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11464
  have eq12244 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq12251 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11466 eq55
    | exact resolve eq55 eq11466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11466
  have eq12280 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12251
    | exact resolve eq12251 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12251
  have eq12285 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12280
  have eq12619 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq12285
       grind)
    | exact superpose eq12285 eq104
    | exact resolve eq104 eq12285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq12285
  have eq12643 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12619
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12619
    | exact resolve eq12619 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12619
  have eq13045 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12643 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12643
  have eq13048 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13045
    | exact resolve eq13045 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13045
  have eq13049 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13048
  have eq13061 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13049
    | exact resolve eq13049 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13049
  have eq13062 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13061
  have eq14040 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13062 eq55
    | exact resolve eq55 eq13062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13062
  have eq14070 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14040
    | exact resolve eq14040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14040
  have eq14071 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14070
  have eq14072 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14071 eq28
    | exact resolve eq28 eq14071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14071
  have eq15198 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12244 eq117
    | exact resolve eq117 eq12244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq12244
  have eq15212 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15198
  have eq15220 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15212
       have r₂ := eq14072
       grind)
    | exact resolve eq15212 eq14072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15212
  have eq15236 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55 x x
       have i₂ := eq15220
       grind)
    | exact superpose eq15220 eq55
    | exact resolve eq55 eq15220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq15220
  have eq15269 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15236
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15236
    | exact resolve eq15236 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15236
  have eq15275 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15269 eq53
    | exact resolve eq53 eq15269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15269
  have eq15580 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15275
  have eq17933 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15580 eq74
    | exact resolve eq74 eq15580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq15580
  have eq17981 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17933
    | exact resolve eq17933 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17933
  have eq18420 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq17981
       grind)
    | exact superpose eq17981 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq17981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17981
  have eq18437 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18420
  have eq18550 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq799 x
       have i₂ := eq18437
       grind)
    | exact superpose eq18437 eq799
    | exact resolve eq799 eq18437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18437
  have eq18623 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52 eq18550
    | exact resolve eq18550 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18550
  have eq18635 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18623
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18623
    | exact resolve eq18623 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18623
  have eq18636 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18635
  have eq18774 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18636 eq21
    | exact resolve eq21 eq18636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18636
  have eq18900 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18774
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18774
    | exact resolve eq18774 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18774
  have eq19094 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18900 eq14072
    | (have r₁ := eq14072
       have r₂ := eq18900
       grind)
    | exact resolve eq14072 eq18900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14072
  have eq19114 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19094
  have eq19115 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19114
  have eq19180 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19115 eq53
    | exact resolve eq53 eq19115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19115
  have eq19366 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19180 eq803
    | exact resolve eq803 eq19180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq19180
  have eq19442 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53 eq19366
    | exact resolve eq19366 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq19366
  have eq19454 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq19442
    | exact resolve eq19442 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19442
  have eq19598 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19454 eq28
    | exact resolve eq28 eq19454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19454
  have eq19636 : x = (M.op x y) := by
    first
    | (have r₁ := eq19598
       have r₂ := eq18900
       grind)
    | exact resolve eq19598 eq18900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18900 eq19598
  have eq19640 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19636 eq21
    | exact resolve eq21 eq19636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq19643 : x = (M.op x x) := by
    first
    | exact superpose eq19636 eq52
    | exact resolve eq52 eq19636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19779 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19640
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19640
    | exact resolve eq19640 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19640
  have eq19784 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq19779 eq27
    | exact resolve eq27 eq19779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq19952 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq799 x
       have i₂ := eq19643
       grind)
    | exact superpose eq19643 eq799
    | exact resolve eq799 eq19643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq19954 : x = (k x x) := by grind
  clear eq19643
  have eq20021 : y = (M.op x y) := by
    first
    | exact superpose eq52 eq19952
    | exact resolve eq19952 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq19952
  have eq20033 : y = (M.op x y) := by
    first
    | (have i₁ := eq20021
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20021
    | exact resolve eq20021 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20021
  have eq20045 : x = y := by
    first
    | exact superpose eq19636 eq20033
    | exact resolve eq20033 eq19636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19636 eq20033
  have eq20055 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20045
       grind)
    | exact superpose eq20045 eq25
    | exact resolve eq25 eq20045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20045
  have eq20182 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20055
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20055
    | exact resolve eq20055 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20055
  have eq20236 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19779 eq20182
    | exact resolve eq20182 eq19779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20182
  have eq20744 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20236 eq19784
    | exact resolve eq19784 eq20236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19784 eq20236
  have eq21211 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq679 x x
       have i₂ := eq19954
       grind)
    | exact superpose eq19954 eq679
    | (have j0 := eq679 x x
       grind)
    | exact resolve eq679 eq19954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq19954
  have eq21214 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21211
  have eq21215 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21214
  have eq21229 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21215
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21215
    | exact resolve eq21215 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21215
  have eq21244 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19779 eq21229
    | exact resolve eq21229 eq19779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19779 eq21229
  have eq21909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20744 eq21244
    | exact resolve eq21244 eq20744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20744 eq21244
  have eq21910 : False := by grind
  exact eq21910

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq108 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq119
    | exact resolve eq119 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq120
    | exact resolve eq120 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq668 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq62 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq62 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq62 X0 X0
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq674 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq668 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq676 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq674 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq674 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq674 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq674 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq686 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq676
    | (have j0 := eq676 X0 X1
       grind)
    | exact resolve eq676 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq806 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x X0 y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ x) X0 (σ y)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq12490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq121 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12490
    | exact resolve eq12490 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12490
  have eq12502 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12491
       have r₂ := eq28
       grind)
    | exact resolve eq12491 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12491
  have eq12504 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12502
    | exact resolve eq12502 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12502
  have eq12509 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq12516 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12504 eq55
    | exact resolve eq55 eq12504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12504
  have eq12546 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12516
    | exact resolve eq12516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12516
  have eq12557 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12546
  have eq12893 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq12557
       grind)
    | exact superpose eq12557 eq108
    | exact resolve eq108 eq12557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq12557
  have eq12917 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12893
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12893
    | exact resolve eq12893 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12893
  have eq13323 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12917 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12917
  have eq13326 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13323
    | exact resolve eq13323 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13323
  have eq13327 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13326
  have eq13339 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13327
    | exact resolve eq13327 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13327
  have eq13340 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13339
  have eq13353 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13340 eq55
    | exact resolve eq55 eq13340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13340
  have eq13383 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13353
    | exact resolve eq13353 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13353
  have eq13384 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13383
  have eq14354 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13384 eq28
    | exact resolve eq28 eq13384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13384
  have eq15211 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12509 eq121
    | exact resolve eq121 eq12509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq12509
  have eq15225 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15211
  have eq15233 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15225
       have r₂ := eq14354
       grind)
    | exact resolve eq15225 eq14354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15225
  have eq15249 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55 x x
       have i₂ := eq15233
       grind)
    | exact superpose eq15233 eq55
    | exact resolve eq55 eq15233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq15233
  have eq15280 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15249
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15249
    | exact resolve eq15249 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15249
  have eq15286 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15280 eq53
    | exact resolve eq53 eq15280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15280
  have eq15784 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15286
  have eq17904 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15784 eq74
    | exact resolve eq74 eq15784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq15784
  have eq17952 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17904
    | exact resolve eq17904 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17904
  have eq18644 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq17952
       grind)
    | exact superpose eq17952 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq17952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17952
  have eq18661 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18644
  have eq18774 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq806 x
       have i₂ := eq18661
       grind)
    | exact superpose eq18661 eq806
    | exact resolve eq806 eq18661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18661
  have eq18846 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52 eq18774
    | exact resolve eq18774 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18774
  have eq18857 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18846
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18846
    | exact resolve eq18846 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18846
  have eq18858 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18857
  have eq19002 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18858 eq21
    | exact resolve eq21 eq18858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18858
  have eq19128 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19002
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19002
    | exact resolve eq19002 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19002
  have eq19325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19128 eq14354
    | (have r₁ := eq14354
       have r₂ := eq19128
       grind)
    | exact resolve eq14354 eq19128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14354
  have eq19345 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19325
  have eq19346 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19345
  have eq19409 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19346 eq53
    | exact resolve eq53 eq19346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19346
  have eq19694 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19409 eq810
    | exact resolve eq810 eq19409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq19409
  have eq19769 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53 eq19694
    | exact resolve eq19694 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq19694
  have eq19780 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq19769
    | exact resolve eq19769 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19769
  have eq19919 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19780 eq28
    | exact resolve eq28 eq19780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19780
  have eq19957 : x = (M.op x y) := by
    first
    | (have r₁ := eq19919
       have r₂ := eq19128
       grind)
    | exact resolve eq19919 eq19128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19128 eq19919
  have eq19961 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19957 eq21
    | exact resolve eq21 eq19957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq19964 : x = (M.op x x) := by
    first
    | exact superpose eq19957 eq52
    | exact resolve eq52 eq19957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20101 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19961
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19961
    | exact resolve eq19961 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19961
  have eq20106 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20101 eq27
    | exact resolve eq27 eq20101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq20271 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq806 x
       have i₂ := eq19964
       grind)
    | exact superpose eq19964 eq806
    | exact resolve eq806 eq19964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq20273 : x = (k x x) := by grind
  clear eq19964
  have eq20339 : y = (M.op x y) := by
    first
    | exact superpose eq52 eq20271
    | exact resolve eq20271 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq20271
  have eq20350 : y = (M.op x y) := by
    first
    | (have i₁ := eq20339
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20339
    | exact resolve eq20339 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20339
  have eq20361 : x = y := by
    first
    | exact superpose eq19957 eq20350
    | exact resolve eq20350 eq19957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19957 eq20350
  have eq20372 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20361
       grind)
    | exact superpose eq20361 eq25
    | exact resolve eq25 eq20361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20361
  have eq20499 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20372
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20372
    | exact resolve eq20372 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20372
  have eq20553 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20101 eq20499
    | exact resolve eq20499 eq20101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20499
  have eq21434 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20553 eq20106
    | exact resolve eq20106 eq20553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20106 eq20553
  have eq21597 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq686 x x
       have i₂ := eq20273
       grind)
    | exact superpose eq20273 eq686
    | (have j0 := eq686 x x
       grind)
    | exact resolve eq686 eq20273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq20273
  have eq21600 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21597
  have eq21601 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21600
  have eq21615 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21601
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21601
    | exact resolve eq21601 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21601
  have eq21630 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20101 eq21615
    | exact resolve eq21615 eq20101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20101 eq21615
  have eq22278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21434 eq21630
    | exact resolve eq21630 eq21434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21434 eq21630
  have eq22279 : False := by grind
  exact eq22279
