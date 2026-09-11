import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq61
    | exact resolve eq61 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) ≠ X0 ∨ (k X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2)) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2)
       have i₂ := eq62 X2 X1 X3 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq460 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq561 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq561 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq561
    | (have j0 := eq561 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq561 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18246 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1079 x y
       grind)
    | exact superpose eq1079 eq16
    | (have j1 := eq1079 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1079 x y
       grind)
    | exact resolve eq16 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq18400 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq18246
  have eq21718 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k (M.op X0 X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 (M.op X1 x) X1 x x
       have i₂ := eq69 (M.op X1 x)
       grind)
    | exact superpose eq69 eq246
    | exact resolve eq246 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq21752 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21718 X0 X1
       have i₂ := eq94 (M.op X0 X1) X1
       grind)
    | exact superpose eq94 eq21718
    | (have j0 := eq21718 X0 X1
       grind)
    | exact resolve eq21718 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21718
  have eq31304 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21752 X0 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq21752
    | exact resolve eq21752 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq31912 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21752 (σ y) (σ x)
       have i₂ := eq18400
       grind)
    | exact superpose eq18400 eq21752
    | exact resolve eq21752 eq18400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31922 : (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31912
       have r₂ := eq18400
       grind)
    | exact resolve eq31912 eq18400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31912
  have eq31975 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18400 eq31922
    | exact resolve eq31922 eq18400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18400 eq31922
  have eq31993 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31975
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq31975
    | exact resolve eq31975 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31975
  have eq67240 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21752 (σ x) (σ y)
       have i₂ := eq31993
       grind)
    | exact superpose eq31993 eq21752
    | exact resolve eq21752 eq31993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21752
  have eq67258 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq67240
       have r₂ := eq31993
       grind)
    | exact resolve eq67240 eq31993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67240
  have eq67331 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31993 eq67258
    | exact resolve eq67258 eq31993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31993 eq67258
  have eq67351 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67331
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq67331
    | exact resolve eq67331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67331
  have eq67373 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq67351
       grind)
    | exact superpose eq67351 eq10
    | exact resolve eq10 eq67351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67351
  have eq67526 : (σ x) = (σ (k x x)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67373
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq67373
    | exact resolve eq67373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67373
  have eq67545 : (τ (σ x)) = (k x x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq67526
       grind)
    | exact superpose eq67526 eq10
    | exact resolve eq10 eq67526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67526
  have eq67698 : y = (k y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67545
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq67545
    | exact resolve eq67545 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67545
  have eq67755 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq67698
       grind)
    | exact superpose eq67698 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq67698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67698
  have eq67756 : y = (M.op y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq67755
  have eq67822 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79 y X0
       have i₂ := eq67756
       grind)
    | exact superpose eq67756 eq79
    | exact resolve eq79 eq67756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67920 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq460 y y x
       have i₂ := eq67756
       grind)
    | exact superpose eq67756 eq460
    | exact resolve eq460 eq67756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67756
  have eq68059 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq67920 X0
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq67920
    | exact resolve eq67920 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67920
  have eq70268 : ∀ X0 : G, y = (M.op y x) ∨ x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq68059 eq67822
    | exact resolve eq67822 eq68059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67822 eq68059
  have eq70297 : ∀ X0 : G, y = (M.op y y) ∨ x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq94 y x
       have i₂ := eq70268 X0
       grind)
    | exact superpose eq70268 eq94
    | (have j1 := eq70268 y
       grind)
    | exact resolve eq94 eq70268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70268
  have eq71072 : y ≠ y ∨ x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq70297 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70297
  have eq71073 : y = (M.op y y) ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq71072
  have eq71180 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79 y X0
       have i₂ := eq71073
       grind)
    | exact superpose eq71073 eq79
    | exact resolve eq79 eq71073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71278 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq460 y y x
       have i₂ := eq71073
       grind)
    | exact superpose eq71073 eq460
    | exact resolve eq460 eq71073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71073
  have eq71420 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq71278 X0
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq71278
    | exact resolve eq71278 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71278
  have eq73238 : ∀ X0 : G, x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq71420 eq71180
    | exact resolve eq71180 eq71420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71180 eq71420
  have eq73294 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x x
       have i₂ := eq73238 X0
       grind)
    | exact superpose eq73238 eq14
    | (have j0 := eq14 x x
       have j1 := eq73238 X0
       grind)
    | exact resolve eq14 eq73238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73238
  have eq73295 : ∀ X0 : G, x = (M.op x y) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq73294 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73294
  have eq75392 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq94 x y
       have i₂ := eq73295 X0
       grind)
    | exact superpose eq73295 eq94
    | (have j1 := eq73295 X0
       grind)
    | exact resolve eq94 eq73295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73295
  have eq75529 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq75392 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75392
  have eq75722 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 x X0
       have i₂ := eq75529 X1
       grind)
    | exact superpose eq75529 eq79
    | (have j1 := eq75529 X1
       grind)
    | exact resolve eq79 eq75529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq75820 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq460 x x x
       have i₂ := eq75529 X0
       grind)
    | exact superpose eq75529 eq460
    | (have j1 := eq75529 X1
       grind)
    | exact resolve eq460 eq75529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75529
  have eq75965 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75820 X0 X1
       have i₂ := eq94 x X0
       grind)
    | exact superpose eq94 eq75820
    | (have j0 := eq75820 X0 X1
       grind)
    | exact resolve eq75820 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq75820
  have eq78480 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq75965 eq75722
    | (have j0 := eq75722 X0 X1
       have j1 := eq75965 X0 X1
       grind)
    | exact resolve eq75722 eq75965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75722
  have eq78481 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq78480 eq75965
    | (have j0 := eq75965 X0 X1
       have j1 := eq78480 X0 X1
       grind)
    | exact resolve eq75965 eq78480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75965
  have eq78530 : ∀ X0 : G, y ≠ y ∨ y = (k y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31304 y
       have i₂ := eq78480 X0 y
       grind)
    | exact superpose eq78480 eq31304
    | (have j1 := eq78480 X0 x
       grind)
    | (have r₁ := eq31304 y
       have r₂ := eq78480 X0 y
       grind)
    | (have r₁ := eq31304 x
       have r₂ := eq78480 x x
       grind)
    | exact resolve eq31304 eq78480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78585 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq460 y X1 X0
       have i₂ := eq78480 X2 X0
       grind)
    | exact superpose eq78480 eq460
    | (have j1 := eq78480 X2 X1
       grind)
    | exact resolve eq460 eq78480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq78731 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y y) X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80 y X0
       have i₂ := eq78480 X1 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq78480 eq80
    | (have j1 := eq78480 X1 X1
       grind)
    | exact resolve eq80 eq78480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78923 : ∀ X0 : G, y = (k y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78530 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78530
  have eq79041 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq78480 eq78731
    | (have j0 := eq78731 X0 X1
       have j1 := eq78480 X1 X1
       grind)
    | exact resolve eq78731 eq78480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78731
  have eq79127 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq78480 eq78585
    | (have j0 := eq78585 X0 X1 X2
       have j1 := eq78480 X2 X1
       grind)
    | exact resolve eq78585 eq78480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78585
  have eq79272 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq78480 eq79041
    | (have j0 := eq79041 X0 X1
       have j1 := eq78480 X1 X1
       grind)
    | exact resolve eq79041 eq78480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79041
  have eq80263 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq78481 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78481
  have eq80264 : x = (M.op y x) := by grind
  clear eq80263
  have eq81251 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op y X0) x) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 y x X1
       have i₂ := eq80264
       grind)
    | exact superpose eq80264 eq61
    | exact resolve eq61 eq80264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80264
  have eq81914 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq561 y y
       have i₂ := eq78923 X0
       grind)
    | exact superpose eq78923 eq561
    | (have j0 := eq561 y y
       have j1 := eq78923 X0
       grind)
    | exact resolve eq561 eq78923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78923
  have eq81917 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq81914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81914
  have eq82783 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq79272 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82784 : y = (M.op x y) := by grind
  clear eq82783
  have eq83758 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82784
       grind)
    | exact superpose eq82784 eq16
    | exact resolve eq16 eq82784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83767 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) y) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 x y X1
       have i₂ := eq82784
       grind)
    | exact superpose eq82784 eq61
    | exact resolve eq61 eq82784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq82784
  have eq91846 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq81917 X1
       grind)
    | exact superpose eq81917 eq9
    | (have j1 := eq81917 X1
       grind)
    | exact resolve eq9 eq81917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81917
  have eq92085 : ∀ X0 X1 : G, (M.op (σ y) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq79127 eq91846
    | (have j0 := eq91846 X0 X1
       have j1 := eq79127 X0 X1 X1
       grind)
    | exact resolve eq91846 eq79127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79127 eq91846
  have eq94281 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op x (σ y)) y) X0) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83767 (σ y) X0
       have i₂ := eq92085 (M.op (M.op (M.op x (σ y)) y) X0) X1
       grind)
    | exact superpose eq92085 eq83767
    | (have j1 := eq92085 X0 X1
       grind)
    | exact resolve eq83767 eq92085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83767 eq92085
  have eq94499 : ∀ X0 X1 : G, (σ y) = (M.op (M.op y X0) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq79272 eq94281
    | (have j0 := eq94281 X0 X1
       have j1 := eq79272 X0 X1
       grind)
    | exact resolve eq94281 eq79272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79272 eq94281
  have eq94507 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq78480 eq94499
    | (have j0 := eq94499 X0 X1
       have j1 := eq78480 X1 X1
       grind)
    | exact resolve eq94499 eq78480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78480 eq94499
  have eq97786 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq83758
       have i₂ := eq94507 (σ x) X0
       grind)
    | exact superpose eq94507 eq83758
    | (have j1 := eq94507 X0 X0
       grind)
    | (have r₁ := eq83758
       have r₂ := eq94507 (σ x) x
       grind)
    | exact resolve eq83758 eq94507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94507
  have eq97835 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq97786 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97786
  have eq98782 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq31304 x
       have i₂ := eq97835 x
       grind)
    | exact superpose eq97835 eq31304
    | (have r₁ := eq31304 x
       have r₂ := eq97835 x
       grind)
    | exact resolve eq31304 eq97835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31304
  have eq98988 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq80 x X0
       have i₂ := eq97835 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq97835 eq80
    | exact resolve eq80 eq97835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq99182 : x = (k x x) := by grind
  clear eq98782
  have eq99301 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq98988 X0
       have i₂ := eq97835 x
       grind)
    | exact superpose eq97835 eq98988
    | exact resolve eq98988 eq97835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98988
  have eq99539 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq99301 X0
       have i₂ := eq97835 X0
       grind)
    | exact superpose eq97835 eq99301
    | exact resolve eq99301 eq97835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99301
  have eq99747 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq561 x x
       have i₂ := eq99182
       grind)
    | exact superpose eq99182 eq561
    | (have j0 := eq561 x x
       grind)
    | exact resolve eq561 eq99182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq99182
  have eq99750 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq99747
  have eq99780 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81251 X0 X1
       have i₂ := eq99539 (M.op y X0)
       grind)
    | exact superpose eq99539 eq81251
    | exact resolve eq81251 eq99539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81251 eq99539
  have eq101224 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99780 X0 X1
       have i₂ := eq97835 X1
       grind)
    | exact superpose eq97835 eq99780
    | exact resolve eq99780 eq97835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97835 eq99780
  have eq102109 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq99750
       grind)
    | exact superpose eq99750 eq9
    | exact resolve eq9 eq99750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99750
  have eq102275 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq102109 X0
       have i₂ := eq101224 (σ x) X0
       grind)
    | exact superpose eq101224 eq102109
    | exact resolve eq102109 eq101224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101224 eq102109
  have eq102336 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq83758
       have i₂ := eq102275 (σ y)
       grind)
    | exact superpose eq102275 eq83758
    | (have r₁ := eq83758
       have r₂ := eq102275 (σ y)
       grind)
    | exact resolve eq83758 eq102275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83758 eq102275
  have eq102562 : False := by grind
  exact eq102562

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq65 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  clear eq36
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq75
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq75 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq131 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq165 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq206 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq382 (M.op X0 X1)
       grind)
    | exact superpose eq382 eq52
    | exact resolve eq52 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq99 eq69
    | (have j0 := eq69 (σ y) (σ x)
       grind)
    | exact resolve eq69 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq732
    | exact resolve eq732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq736 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq733
       have r₂ := eq27
       grind)
    | exact resolve eq733 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq739 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq736 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq736
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq736
       grind)
    | exact resolve eq13 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq747 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq739
  have eq752 : (τ (σ y)) = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq747 eq59
    | exact resolve eq59 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq747
  have eq754 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq752
    | exact resolve eq752 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq752
  have eq766 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq69 x y
       have i₂ := eq754
       grind)
    | exact superpose eq754 eq69
    | (have j0 := eq69 y x
       grind)
    | exact resolve eq69 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq767 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq766
  have eq769 : y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq810 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq769
       grind)
    | exact superpose eq769 eq14
    | exact resolve eq14 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq769
       grind)
    | exact superpose eq769 eq14
    | exact resolve eq14 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq387 y x
       have i₂ := eq769
       grind)
    | exact superpose eq769 eq387
    | exact resolve eq387 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq821 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq818
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq818
    | exact resolve eq818 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq965 : x = (M.op (M.op y y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq810 x
       have i₂ := eq769
       grind)
    | exact superpose eq769 eq810
    | exact resolve eq810 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : x = (M.op (M.op y y) x) ∨ x = (M.op x y) := by grind
  clear eq965
  have eq1010 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq811 y
       have i₂ := eq382 y
       grind)
    | exact superpose eq382 eq811
    | exact resolve eq811 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq811
  have eq1029 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq979
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq979
    | exact resolve eq979 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq1010
  have eq1048 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1029
  have eq1090 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq769
       have i₂ := eq1048
       grind)
    | exact superpose eq1048 eq769
    | exact resolve eq769 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq1092 : x = (M.op (M.op y x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq810 x
       have i₂ := eq1048
       grind)
    | exact superpose eq1048 eq810
    | exact resolve eq810 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq1106 : x = (M.op (M.op y x) x) ∨ x = (M.op x y) := by grind
  clear eq1092
  have eq1108 : x = (M.op x y) ∨ x = y := by grind
  clear eq1090
  have eq1122 : y = (M.op (M.op x x) y) ∨ x = y := by
    first
    | exact superpose eq1108 eq206
    | exact resolve eq206 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq1340 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1106
       have i₂ := eq1048
       grind)
    | exact superpose eq1048 eq1106
    | exact resolve eq1106 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048 eq1106
  have eq1356 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1340
  have eq1365 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq1356
       grind)
    | exact superpose eq1356 eq50
    | exact resolve eq50 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1356
  have eq2391 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq821 eq1365
    | exact resolve eq1365 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq1365
  have eq2405 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2391
  have eq2406 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2405
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2405
    | exact resolve eq2405 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2445 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2406
  have eq2447 : x = (M.op x y) := by
    first
    | (have r₁ := eq2445
       have r₂ := eq1108
       grind)
    | exact resolve eq2445 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq2445
  have eq2462 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2447 eq20
    | exact resolve eq20 eq2447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2466 : x ≠ x ∨ x = (k y x) := by
    first
    | exact superpose eq2447 eq65
    | (have r₁ := eq65
       have r₂ := eq2447
       grind)
    | exact resolve eq65 eq2447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2488 : x = (k y x) := by grind
  clear eq2466
  have eq2500 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2462
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2462
    | exact resolve eq2462 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462
  have eq2503 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2500 eq26
    | exact resolve eq26 eq2500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2552 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq2488
       grind)
    | exact superpose eq2488 eq75
    | exact resolve eq75 eq2488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq2488
  have eq2555 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2500 eq2552
    | exact resolve eq2552 eq2500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq2557 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2555
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2555
    | exact resolve eq2555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555
  have eq2558 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2500 eq2557
    | exact resolve eq2557 eq2500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq2578 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2558 eq69
    | (have j0 := eq69 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq69 eq2558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2503 eq2578
    | exact resolve eq2578 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq2582 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2579
       have r₂ := eq27
       grind)
    | exact resolve eq2579 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq2587 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2582 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq2582
       grind)
    | exact resolve eq12 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582
  have eq2601 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2587
  have eq2603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2503 eq2601
    | exact resolve eq2601 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601
  have eq2604 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2603
       have r₂ := eq27
       grind)
    | exact resolve eq2603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2605 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2558 eq2604
    | exact resolve eq2604 eq2558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558 eq2604
  have eq2628 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2605 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq2605
       grind)
    | exact resolve eq13 eq2605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2641 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2628
  have eq2774 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2641 eq165
    | exact resolve eq165 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq2641
  have eq2778 : (τ (σ (M.op x y))) = (k x x) := by
    first
    | exact superpose eq2447 eq2774
    | exact resolve eq2774 eq2447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq2779 : (M.op x y) = (k x x) := by
    first
    | exact superpose eq30 eq2778
    | exact resolve eq2778 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2778
  have eq2780 : x = (k x x) := by
    first
    | exact superpose eq2447 eq2779
    | exact resolve eq2779 eq2447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2779
  have eq2783 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69 x x
       have i₂ := eq2780
       grind)
    | exact superpose eq2780 eq69
    | (have j0 := eq69 x x
       grind)
    | exact resolve eq69 eq2780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2780
  have eq2784 : x = (M.op x x) := by grind
  clear eq2783
  have eq2931 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1122
       have i₂ := eq2784
       grind)
    | exact superpose eq2784 eq1122
    | exact resolve eq1122 eq2784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122 eq2784
  have eq2959 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2931
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2931
    | exact resolve eq2931 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2931
  have eq2965 : x = y ∨ x = y := by
    first
    | exact superpose eq2447 eq2959
    | exact resolve eq2959 eq2447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447 eq2959
  have eq2966 : x = y := by grind
  clear eq2965
  have eq2970 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2966
       grind)
    | exact superpose eq2966 eq24
    | exact resolve eq24 eq2966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2966
  have eq3026 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2970
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2970
    | exact resolve eq2970 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2970
  have eq3040 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2500 eq3026
    | exact resolve eq3026 eq2500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500 eq3026
  have eq3089 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3040 eq2503
    | exact resolve eq2503 eq3040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503 eq3040
  have eq3093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2605 eq3089
    | exact resolve eq3089 eq2605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2605 eq3089
  have eq3110 : False := by grind
  exact eq3110

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  clear eq17
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq61
    | exact resolve eq61 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq574 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq574 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq574
    | (have j0 := eq574 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq574 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq15157 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1062 x y
       grind)
    | exact superpose eq1062 eq16
    | (have j1 := eq1062 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1062 x y
       grind)
    | exact resolve eq16 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq15306 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq15157
  have eq33995 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90 (σ y) (σ x)
       have i₂ := eq15306
       grind)
    | exact superpose eq15306 eq90
    | exact resolve eq90 eq15306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15306
  have eq78484 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) (τ X1)
       have i₂ := eq575 X0 X1
       grind)
    | exact superpose eq575 eq12
    | (have j0 := eq12 (τ X0) (τ X1)
       have j1 := eq575 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) (τ X0)
       have r₂ := eq575 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) (τ X1)
       have r₂ := eq575 X0 X1
       grind)
    | exact resolve eq12 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq78746 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78484 X0 X1
       have j1 := eq12 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq78484 X0 X1
       have r₂ := eq12 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq78484 X0 X1
       have r₂ := eq12 (τ X0) (τ X1)
       grind)
    | exact resolve eq78484 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78484
  have eq78774 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78746 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq78746
    | (have j0 := eq78746 X0 X1
       grind)
    | exact resolve eq78746 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq78746
  have eq79554 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq78774 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq78774
    | (have j0 := eq78774 (σ X0) (σ X1)
       grind)
    | exact resolve eq78774 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78774
  have eq79614 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq79554 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq79554
    | (have j0 := eq79554 X0 X1
       grind)
    | exact resolve eq79554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79554
  have eq79641 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq79614 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq79614
    | (have j0 := eq79614 X0 X1
       grind)
    | exact resolve eq79614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79614
  have eq79662 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq79641 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79641
    | (have j0 := eq79641 X0 X1
       grind)
    | exact resolve eq79641 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79641
  have eq79682 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq79662 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq79662
    | (have j0 := eq79662 X0 X1
       grind)
    | exact resolve eq79662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79662
  have eq79697 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79682 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq79682
    | (have j0 := eq79682 X0 X1
       grind)
    | exact resolve eq79682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79682
  have eq79712 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79697 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79697
    | (have j0 := eq79697 X0 X1
       grind)
    | exact resolve eq79697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79697
  have eq79741 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79712 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq79712
    | (have j0 := eq79712 (σ X0) (σ X1)
       grind)
    | exact resolve eq79712 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80938 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107 (σ y) (σ y)
       have i₂ := eq33995
       grind)
    | exact superpose eq33995 eq107
    | (have r₁ := eq107 (σ y) (σ y)
       have r₂ := eq33995
       grind)
    | (have r₁ := eq107 (σ x) (σ y)
       have r₂ := eq33995
       grind)
    | (have r₁ := eq107 y x
       have r₂ := eq33995
       grind)
    | exact resolve eq107 eq33995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33995
  have eq81099 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq80938
  have eq81160 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81099
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq81099
    | exact resolve eq81099 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81099
  have eq81251 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90 (σ x) (σ y)
       have i₂ := eq81160
       grind)
    | exact superpose eq81160 eq90
    | exact resolve eq90 eq81160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81160
  have eq81615 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107 (σ x) (σ x)
       have i₂ := eq81251
       grind)
    | exact superpose eq81251 eq107
    | (have r₁ := eq107 (σ x) (σ x)
       have r₂ := eq81251
       grind)
    | (have r₁ := eq107 y x
       have r₂ := eq81251
       grind)
    | (have r₁ := eq107 x y
       have r₂ := eq81251
       grind)
    | exact resolve eq107 eq81251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq81251
  have eq81776 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq81615
  have eq81838 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81776
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq81776
    | exact resolve eq81776 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81776
  have eq81917 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq81838
       grind)
    | exact superpose eq81838 eq10
    | exact resolve eq10 eq81838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81838
  have eq82080 : (σ x) = (σ (k x x)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81917
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq81917
    | exact resolve eq81917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81917
  have eq82109 : (τ (σ x)) = (k x x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq82080
       grind)
    | exact superpose eq82080 eq10
    | exact resolve eq10 eq82080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82080
  have eq82272 : y = (k y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82109
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq82109
    | exact resolve eq82109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82109
  have eq82348 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79712 y y
       have i₂ := eq82272
       grind)
    | exact superpose eq82272 eq79712
    | (have j0 := eq79712 y y
       grind)
    | (have r₁ := eq79712 y y
       have r₂ := eq82272
       grind)
    | (have r₁ := eq79712 x x
       have r₂ := eq82272
       grind)
    | exact resolve eq79712 eq82272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82272
  have eq82352 : y ≠ y ∨ y = (M.op y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq82348
  have eq82353 : y = (M.op y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq82352
  have eq82447 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq82353
       grind)
    | exact superpose eq82353 eq76
    | exact resolve eq76 eq82353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82544 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq471 y y x
       have i₂ := eq82353
       grind)
    | exact superpose eq82353 eq471
    | exact resolve eq471 eq82353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82353
  have eq82733 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq82544 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq82544
    | exact resolve eq82544 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82544
  have eq84481 : ∀ X0 : G, y = (M.op y x) ∨ x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq82733 eq82447
    | exact resolve eq82447 eq82733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82447 eq82733
  have eq84510 : ∀ X0 : G, y = (M.op y y) ∨ x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90 y x
       have i₂ := eq84481 X0
       grind)
    | exact superpose eq84481 eq90
    | (have j1 := eq84481 y
       grind)
    | exact resolve eq90 eq84481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84481
  have eq85332 : y ≠ y ∨ x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq84510 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84510
  have eq85333 : y = (M.op y y) ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq85332
  have eq85456 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq85333
       grind)
    | exact superpose eq85333 eq76
    | exact resolve eq76 eq85333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85553 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq471 y y x
       have i₂ := eq85333
       grind)
    | exact superpose eq85333 eq471
    | exact resolve eq471 eq85333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85333
  have eq85742 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq85553 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq85553
    | exact resolve eq85553 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85553
  have eq87067 : ∀ X0 : G, x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq85742 eq85456
    | exact resolve eq85456 eq85742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85456 eq85742
  have eq87136 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79712 x x
       have i₂ := eq87067 X0
       grind)
    | exact superpose eq87067 eq79712
    | (have j0 := eq79712 x x
       have j1 := eq87067 X0
       grind)
    | (have r₁ := eq79712 x x
       have r₂ := eq87067 X0
       grind)
    | exact resolve eq79712 eq87067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79712 eq87067
  have eq87140 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq87136 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87136
  have eq87141 : ∀ X0 : G, x = (M.op x y) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq87140 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87140
  have eq89478 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq90 x y
       have i₂ := eq87141 X0
       grind)
    | exact superpose eq87141 eq90
    | (have j1 := eq87141 X0
       grind)
    | exact resolve eq90 eq87141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87141
  have eq89642 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq89478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89478
  have eq89860 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 x X0
       have i₂ := eq89642 X1
       grind)
    | exact superpose eq89642 eq76
    | (have j1 := eq89642 X1
       grind)
    | exact resolve eq76 eq89642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq89957 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq471 x x x
       have i₂ := eq89642 X0
       grind)
    | exact superpose eq89642 eq471
    | (have j1 := eq89642 X1
       grind)
    | exact resolve eq471 eq89642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89642
  have eq90145 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89957 X0 X1
       have i₂ := eq90 x X0
       grind)
    | exact superpose eq90 eq89957
    | (have j0 := eq89957 X0 X1
       grind)
    | exact resolve eq89957 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq89957
  have eq91465 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq90145 eq89860
    | (have j0 := eq89860 X0 X1
       have j1 := eq90145 X0 X1
       grind)
    | exact resolve eq89860 eq90145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89860
  have eq91466 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq91465 eq90145
    | (have j0 := eq90145 X0 X1
       have j1 := eq91465 X0 X1
       grind)
    | exact resolve eq90145 eq91465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90145
  have eq91470 : ∀ X0 : G, y ≠ y ∨ (k y y) = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 y
       have i₂ := eq91465 X0 y
       grind)
    | exact superpose eq91465 eq75
    | (have j1 := eq91465 X0 x
       grind)
    | (have r₁ := eq75 y
       have r₂ := eq91465 X0 y
       grind)
    | (have r₁ := eq75 x
       have r₂ := eq91465 x x
       grind)
    | exact resolve eq75 eq91465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91570 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq471 y X1 X0
       have i₂ := eq91465 X2 X0
       grind)
    | exact superpose eq91465 eq471
    | (have j1 := eq91465 X2 X1
       grind)
    | exact resolve eq471 eq91465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq91744 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y y) X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq91465 X1 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq91465 eq77
    | (have j1 := eq91465 X1 X1
       grind)
    | exact resolve eq77 eq91465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91944 : ∀ X0 : G, (k y y) = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq91470 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91470
  have eq92063 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq91465 eq91744
    | (have j0 := eq91744 X0 X1
       have j1 := eq91465 X1 X1
       grind)
    | exact resolve eq91744 eq91465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91744
  have eq92174 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq91465 eq91570
    | (have j0 := eq91570 X0 X1 X2
       have j1 := eq91465 X2 X1
       grind)
    | exact resolve eq91570 eq91465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91570
  have eq92250 : ∀ X0 : G, y = (k y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq91465 eq91944
    | (have j0 := eq91944 X0
       have j1 := eq91465 X0 x
       grind)
    | exact resolve eq91944 eq91465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91944
  have eq92318 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq91465 eq92063
    | (have j0 := eq92063 X0 X1
       have j1 := eq91465 X1 X1
       grind)
    | exact resolve eq92063 eq91465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92063
  have eq93399 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq91466 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91466
  have eq93400 : x = (M.op y x) := by grind
  clear eq93399
  have eq94455 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op y X0) x) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 y x X1
       have i₂ := eq93400
       grind)
    | exact superpose eq93400 eq61
    | exact resolve eq61 eq93400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93400
  have eq95204 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq79741 y y
       have i₂ := eq92250 X0
       grind)
    | exact superpose eq92250 eq79741
    | (have j0 := eq79741 y y
       have j1 := eq92250 X0
       grind)
    | exact resolve eq79741 eq92250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92250
  have eq95205 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq95204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95204
  have eq95206 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq95205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95205
  have eq96182 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq92318 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96183 : y = (M.op x y) := by grind
  clear eq96182
  have eq97227 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96183
       grind)
    | exact superpose eq96183 eq16
    | exact resolve eq16 eq96183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97236 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) y) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 x y X1
       have i₂ := eq96183
       grind)
    | exact superpose eq96183 eq61
    | exact resolve eq61 eq96183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq96183
  have eq104408 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq95206 X1
       grind)
    | exact superpose eq95206 eq9
    | (have j1 := eq95206 X1
       grind)
    | exact resolve eq9 eq95206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95206
  have eq104673 : ∀ X0 X1 : G, (M.op (σ y) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq92174 eq104408
    | (have j0 := eq104408 X0 X1
       have j1 := eq92174 X0 X1 X1
       grind)
    | exact resolve eq104408 eq92174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92174 eq104408
  have eq107009 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op x (σ y)) y) X0) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97236 (σ y) X0
       have i₂ := eq104673 (M.op (M.op (M.op x (σ y)) y) X0) X1
       grind)
    | exact superpose eq104673 eq97236
    | (have j1 := eq104673 X0 X1
       grind)
    | exact resolve eq97236 eq104673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97236 eq104673
  have eq107247 : ∀ X0 X1 : G, (σ y) = (M.op (M.op y X0) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq92318 eq107009
    | (have j0 := eq107009 X0 X1
       have j1 := eq92318 X0 X1
       grind)
    | exact resolve eq107009 eq92318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92318 eq107009
  have eq107255 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq91465 eq107247
    | (have j0 := eq107247 X0 X1
       have j1 := eq91465 X1 X1
       grind)
    | exact resolve eq107247 eq91465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91465 eq107247
  have eq110761 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq97227
       have i₂ := eq107255 (σ x) X0
       grind)
    | exact superpose eq107255 eq97227
    | (have j1 := eq107255 X0 X0
       grind)
    | (have r₁ := eq97227
       have r₂ := eq107255 (σ x) x
       grind)
    | exact resolve eq97227 eq107255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107255
  have eq110818 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq110761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110761
  have eq111754 : x ≠ x ∨ (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq75 x
       have i₂ := eq110818 x
       grind)
    | exact superpose eq110818 eq75
    | (have r₁ := eq75 x
       have r₂ := eq110818 x
       grind)
    | exact resolve eq75 eq110818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq112029 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq77 x X0
       have i₂ := eq110818 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq110818 eq77
    | exact resolve eq77 eq110818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq112230 : (k x x) = (M.op x x) := by grind
  clear eq111754
  have eq112350 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq112029 X0
       have i₂ := eq110818 x
       grind)
    | exact superpose eq110818 eq112029
    | exact resolve eq112029 eq110818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112029
  have eq112537 : x = (k x x) := by
    first
    | (have i₁ := eq112230
       have i₂ := eq110818 x
       grind)
    | exact superpose eq110818 eq112230
    | exact resolve eq112230 eq110818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112230
  have eq112607 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq112350 X0
       have i₂ := eq110818 X0
       grind)
    | exact superpose eq110818 eq112350
    | exact resolve eq112350 eq110818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112350
  have eq112838 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79741 x x
       have i₂ := eq112537
       grind)
    | exact superpose eq112537 eq79741
    | (have j0 := eq79741 x x
       grind)
    | exact resolve eq79741 eq112537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79741 eq112537
  have eq112839 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq112838
  have eq112840 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq112839
  have eq112899 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94455 X0 X1
       have i₂ := eq112607 (M.op y X0)
       grind)
    | exact superpose eq112607 eq94455
    | exact resolve eq94455 eq112607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94455 eq112607
  have eq114440 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq112899 X0 X1
       have i₂ := eq110818 X1
       grind)
    | exact superpose eq110818 eq112899
    | exact resolve eq112899 eq110818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110818 eq112899
  have eq115372 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq112840
       grind)
    | exact superpose eq112840 eq9
    | exact resolve eq9 eq112840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112840
  have eq115557 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq115372 X0
       have i₂ := eq114440 (σ x) X0
       grind)
    | exact superpose eq114440 eq115372
    | exact resolve eq115372 eq114440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114440 eq115372
  have eq115620 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq97227
       have i₂ := eq115557 (σ y)
       grind)
    | exact superpose eq115557 eq97227
    | (have r₁ := eq97227
       have r₂ := eq115557 (σ y)
       grind)
    | exact resolve eq97227 eq115557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97227 eq115557
  have eq115856 : False := by grind
  exact eq115856

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyy_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq61
    | exact resolve eq61 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq79 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 X1) X0 X2 X3
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq62
    | exact resolve eq62 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq420 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq646 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq646 y x
       grind)
    | exact superpose eq646 eq16
    | (have j1 := eq646 y x
       grind)
    | exact resolve eq16 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X1) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq646 X0 X1
       grind)
    | exact superpose eq646 eq9
    | (have j1 := eq646 X0 X1
       grind)
    | exact resolve eq9 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq931 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq646 X0 X1
       grind)
    | exact superpose eq646 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq646 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq646 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq646 X0 X1
       grind)
    | exact resolve eq12 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq646 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq646 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq959 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq957 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq970 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq931 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq931 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq931 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq931 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq974 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq970 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq970
    | (have j0 := eq970 X0 X1
       grind)
    | exact resolve eq970 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq979 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq959 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq959
    | (have j0 := eq959 (τ X0)
       grind)
    | exact resolve eq959 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq959
  have eq981 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq979 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq979
    | (have j0 := eq979 X0
       grind)
    | exact resolve eq979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq984 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq981 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq981
    | (have j0 := eq981 X0
       grind)
    | exact resolve eq981 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq6476 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq958 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq958
    | (have j0 := eq958 (τ X1) (τ X0)
       grind)
    | exact resolve eq958 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq6497 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6476 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6476
    | (have j0 := eq6476 X0 X1
       grind)
    | exact resolve eq6476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6476
  have eq6506 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6497 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6497
    | (have j0 := eq6497 X0 X1
       grind)
    | exact resolve eq6497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6497
  have eq6514 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6506 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6506
    | (have j0 := eq6506 X0 X1
       grind)
    | exact resolve eq6506 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6506
  have eq6521 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6514 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6514
    | (have j0 := eq6514 X0 X1
       grind)
    | exact resolve eq6514 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514
  have eq6528 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6521 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6521
    | (have j0 := eq6521 X0 X1
       grind)
    | exact resolve eq6521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6521
  have eq6533 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6528 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6528
    | (have j0 := eq6528 X0 X1
       grind)
    | exact resolve eq6528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6528
  have eq6534 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq928
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq928
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq928 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq6537 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq6534
  have eq6815 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X1)) X2) (σ (τ (k X0 X1)))) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq930 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq930
    | (have j0 := eq930 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq930 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq930
  have eq6922 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X1)) X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6815 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6815
    | (have j0 := eq6815 X0 X1 X2
       grind)
    | exact resolve eq6815 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6815
  have eq6932 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6922 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6922
    | (have j0 := eq6922 X0 X1 X2
       grind)
    | exact resolve eq6922 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6922
  have eq6940 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6932 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6932
    | (have j0 := eq6932 X0 X1 X2
       grind)
    | exact resolve eq6932 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6932
  have eq6947 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6940 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6940
    | (have j0 := eq6940 X0 X1 X2
       grind)
    | exact resolve eq6940 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6940
  have eq6954 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6947 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6947
    | (have j0 := eq6947 X0 X1 X2
       grind)
    | exact resolve eq6947 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6947
  have eq6959 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6954 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6954
    | (have j0 := eq6954 X0 X1 X2
       grind)
    | exact resolve eq6954 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6954
  have eq89868 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq6537
       grind)
    | exact superpose eq6537 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6537
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq6537
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6537
       grind)
    | exact resolve eq13 eq6537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6537
  have eq89956 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq89868
  have eq89957 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq89956
  have eq90000 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89957
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq89957
    | exact resolve eq89957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89957
  have eq117949 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (k X1 X0)
       have i₂ := eq6959 X1 X0 X0
       grind)
    | exact superpose eq6959 eq79
    | (have j1 := eq6959 X1 X0 x
       grind)
    | exact resolve eq79 eq6959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6959
  have eq1532181 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94 (σ x) (σ y)
       have i₂ := eq90000
       grind)
    | exact superpose eq90000 eq94
    | exact resolve eq94 eq90000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90000
  have eq1692143 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq112 (σ x) (σ x)
       have i₂ := eq1532181
       grind)
    | exact superpose eq1532181 eq112
    | (have r₁ := eq112 (σ x) (σ x)
       have r₂ := eq1532181
       grind)
    | (have r₁ := eq112 y x
       have r₂ := eq1532181
       grind)
    | (have r₁ := eq112 x y
       have r₂ := eq1532181
       grind)
    | exact resolve eq112 eq1532181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532181
  have eq1692806 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1692143
  have eq1693100 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1692806
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1692806
    | exact resolve eq1692806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692806
  have eq1693569 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1693100
       grind)
    | exact superpose eq1693100 eq10
    | exact resolve eq10 eq1693100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693100
  have eq1693948 : x = (k y x) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1693569
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1693569
    | exact resolve eq1693569 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693569
  have eq1693952 : (σ x) = (σ (k x x)) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1693948
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq1693948
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1693948 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693948
  have eq1694045 : (τ (σ x)) = (k x x) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq1693952
       grind)
    | exact superpose eq1693952 eq10
    | exact resolve eq10 eq1693952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693952
  have eq1694469 : x = (k y x) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1694045
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1694045
    | exact resolve eq1694045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694045
  have eq1694551 : x ≠ x ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6533 y x
       have i₂ := eq1694469
       grind)
    | exact superpose eq1694469 eq6533
    | (have j0 := eq6533 y x
       grind)
    | (have r₁ := eq6533 y x
       have r₂ := eq1694469
       grind)
    | (have r₁ := eq6533 x x
       have r₂ := eq1694469
       grind)
    | exact resolve eq6533 eq1694469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6533
  have eq1694597 : x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117949 x y
       have i₂ := eq1694469
       grind)
    | exact superpose eq1694469 eq117949
    | (have j0 := eq117949 x x
       grind)
    | exact resolve eq117949 eq1694469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117949 eq1694469
  have eq1694620 : x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq1694597
  have eq1694636 : x ≠ x ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq1694551
  have eq1694637 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq1694636
  have eq1694652 : y = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq984 x
       grind)
    | (have r₁ := eq1694620
       have r₂ := eq984 x
       grind)
    | exact resolve eq1694620 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694620
  have eq1694689 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq1694637
       grind)
    | exact superpose eq1694637 eq9
    | exact resolve eq9 eq1694637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694637
  have eq1695775 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq1694689 X0
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq1694689
    | exact resolve eq1694689 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694689
  have eq1695822 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94 y x
       have i₂ := eq1694652
       grind)
    | exact superpose eq1694652 eq94
    | exact resolve eq94 eq1694652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694652
  have eq1705145 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1695775 y
       have i₂ := eq1695822
       grind)
    | exact superpose eq1695822 eq1695775
    | exact resolve eq1695775 eq1695822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695822
  have eq1706822 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq1705145
  have eq1706829 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq984 x
       grind)
    | (have r₁ := eq1706822
       have r₂ := eq984 x
       grind)
    | exact resolve eq1706822 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706822
  have eq1707444 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1695775 x
       have i₂ := eq1706829
       grind)
    | exact superpose eq1706829 eq1695775
    | exact resolve eq1695775 eq1706829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695775 eq1706829
  have eq1708245 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq1707444
  have eq1708253 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq984 x
       grind)
    | (have r₁ := eq1708245
       have r₂ := eq984 x
       grind)
    | exact resolve eq1708245 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984 eq1708245
  have eq1708286 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94 x y
       have i₂ := eq1708253
       grind)
    | exact superpose eq1708253 eq94
    | exact resolve eq94 eq1708253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708253
  have eq1709078 : x = (M.op x x) := by grind
  clear eq1708286
  have eq1709417 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq79 x X0
       have i₂ := eq1709078
       grind)
    | exact superpose eq1709078 eq79
    | exact resolve eq79 eq1709078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1709621 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq112 x x
       have i₂ := eq1709078
       grind)
    | exact superpose eq1709078 eq112
    | (have r₁ := eq112 x x
       have r₂ := eq1709078
       grind)
    | exact resolve eq112 eq1709078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1709646 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq420 x x x
       have i₂ := eq1709078
       grind)
    | exact superpose eq1709078 eq420
    | exact resolve eq420 eq1709078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709078
  have eq1710284 : x = (k x x) := by grind
  clear eq1709621
  have eq1710556 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1709646 X0
       have i₂ := eq94 x X0
       grind)
    | exact superpose eq94 eq1709646
    | exact resolve eq1709646 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1709646
  have eq1710918 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq974 x x
       have i₂ := eq1710284
       grind)
    | exact superpose eq1710284 eq974
    | (have j0 := eq974 x x
       grind)
    | exact resolve eq974 eq1710284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq1710284
  have eq1711109 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1710918
  have eq1711110 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1711109
  have eq1716044 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1709417 X0
       have i₂ := eq1710556 X0
       grind)
    | exact superpose eq1710556 eq1709417
    | exact resolve eq1709417 eq1710556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709417 eq1710556
  have eq1716269 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op x X1) X0) X2) (M.op x X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq230 x X1 X0 X2
       have i₂ := eq1716044 X0
       grind)
    | exact superpose eq1716044 eq230
    | exact resolve eq230 eq1716044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq1716286 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq420 x X1 X0
       have i₂ := eq1716044 X0
       grind)
    | exact superpose eq1716044 eq420
    | exact resolve eq420 eq1716044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq1719206 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1716286 X0 X0
       have i₂ := eq1716044 X0
       grind)
    | exact superpose eq1716044 eq1716286
    | exact resolve eq1716286 eq1716044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716286
  have eq1719222 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1716269 X0 X0 X2
       have i₂ := eq1716044 X0
       grind)
    | exact superpose eq1716044 eq1716269
    | exact resolve eq1716269 eq1716044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716269
  have eq1904963 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1719222 (σ x) (σ x) X0
       have i₂ := eq1711110
       grind)
    | exact superpose eq1711110 eq1719222
    | exact resolve eq1719222 eq1711110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711110 eq1719222
  have eq1907918 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1904963 X0
       have i₂ := eq1719206 X0 (σ x)
       grind)
    | exact superpose eq1719206 eq1904963
    | exact resolve eq1904963 eq1719206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719206 eq1904963
  have eq1914034 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1907918 (σ y)
       grind)
    | exact superpose eq1907918 eq16
    | exact resolve eq16 eq1907918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907918
  have eq1916820 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1914034
       have i₂ := eq1716044 y
       grind)
    | exact superpose eq1716044 eq1914034
    | exact resolve eq1914034 eq1716044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716044 eq1914034
  have eq1916821 : False := by grind
  exact eq1916821

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxy_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq108 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq114 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq43
    | exact resolve eq43 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq116 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq49
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq117 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq116
    | exact resolve eq116 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq114
    | exact resolve eq114 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
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
       have i₂ := eq111 sF1
       grind)
    | exact superpose eq111 eq138
    | exact resolve eq138 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq144 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq111 sF0
       grind)
    | exact superpose eq111 eq141
    | exact resolve eq141 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq141
  have eq166 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq144 eq16
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq253 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq260 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq516 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq524 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq516 X0
       grind)
    | exact superpose eq516 eq14
    | exact resolve eq14 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq1284 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq524
    | exact resolve eq524 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1286 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq524
    | exact resolve eq524 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq524
  have eq9919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9919
    | exact resolve eq9919 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9919
  have eq9931 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9920
       have r₂ := eq27
       grind)
    | exact resolve eq9920 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9920
  have eq9935 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9931
    | exact resolve eq9931 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9931
  have eq9937 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9935
    | exact resolve eq9935 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9935
  have eq9939 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9937 eq109
    | (have r₁ := eq109
       have r₂ := eq9937
       grind)
    | exact resolve eq109 eq9937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq9937
  have eq10010 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq9939
  have eq10011 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq10010
  have eq10282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10011 eq96
    | exact resolve eq96 eq10011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq10011
  have eq10290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10282
  have eq10292 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10290
       have r₂ := eq27
       grind)
    | exact resolve eq10290 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10290
  have eq10472 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq10292
       grind)
    | exact superpose eq10292 eq108
    | (have r₁ := eq108
       have r₂ := eq10292
       grind)
    | exact resolve eq108 eq10292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq10473 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq10292
       grind)
    | exact superpose eq10292 eq119
    | exact resolve eq119 eq10292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10292
  have eq10543 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10472
  have eq10544 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10543
  have eq10555 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10473
    | exact resolve eq10473 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10473
  have eq10778 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq10544
       grind)
    | exact superpose eq10544 eq74
    | exact resolve eq74 eq10544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq10544
  have eq10792 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10778
    | exact resolve eq10778 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10778
  have eq11163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10792 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10792
  have eq11166 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11163
    | exact resolve eq11163 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11163
  have eq11177 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11166
       have r₂ := eq27
       grind)
    | exact resolve eq11166 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11166
  have eq11181 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11177
    | exact resolve eq11177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11177
  have eq11183 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11181
    | exact resolve eq11181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11181
  have eq11184 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11183
  have eq11783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11184 eq10555
    | exact resolve eq10555 eq11184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10555 eq11184
  have eq11847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11783
  have eq11855 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11847
       have r₂ := eq27
       grind)
    | exact resolve eq11847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11847
  have eq12005 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11855 eq260
    | exact resolve eq260 eq11855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq12028 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11855 eq1286
    | exact resolve eq1286 eq11855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq12051 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12028 eq117
    | exact resolve eq117 eq12028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq12164 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq12051
    | exact resolve eq12051 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12051
  have eq12383 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12028 eq12005
    | exact resolve eq12005 eq12028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12005 eq12028
  have eq12427 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12383
  have eq12430 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12427
    | exact resolve eq12427 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12427
  have eq12463 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12430 eq11855
    | exact resolve eq11855 eq12430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11855 eq12430
  have eq12468 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq12463
  have eq12475 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12468 eq29
    | exact resolve eq29 eq12468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12468
  have eq12606 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq12475
    | exact resolve eq12475 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12475
  have eq12621 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12606 eq20
    | exact resolve eq20 eq12606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12698 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq12606 eq1284
    | exact resolve eq1284 eq12606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq12765 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq12621
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12621
    | exact resolve eq12621 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12621
  have eq13288 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq119
       have i₂ := eq12698
       grind)
    | exact superpose eq12698 eq119
    | exact resolve eq119 eq12698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq12698
  have eq13395 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq13288
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13288
    | exact resolve eq13288 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13288
  have eq14519 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12765 eq13395
    | exact resolve eq13395 eq12765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12765 eq13395
  have eq14602 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq14519
  have eq16547 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14602 eq166
    | exact resolve eq166 eq14602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14602
  have eq16626 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq16547
    | exact resolve eq16547 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16547
  have eq16822 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq16626 eq253
    | exact resolve eq253 eq16626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq16626
  have eq16966 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12606 eq16822
    | exact resolve eq16822 eq12606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16822
  have eq17005 : y = (M.op x y) ∨ x = y := by grind
  clear eq16966
  have eq17007 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq17005
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17005
    | exact resolve eq17005 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17005
  have eq17091 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq17007 eq12606
    | exact resolve eq12606 eq17007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12606 eq17007
  have eq17101 : x = y := by grind
  clear eq17091
  have eq17173 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17101
       grind)
    | exact superpose eq17101 eq18
    | exact resolve eq18 eq17101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq17174 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17101
       grind)
    | exact superpose eq17101 eq24
    | exact resolve eq24 eq17101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17101
  have eq17301 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17174
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17174
    | exact resolve eq17174 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17174
  have eq17318 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17301 eq26
    | exact resolve eq26 eq17301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq17301
  have eq17514 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12164
       have i₂ := eq17173
       grind)
    | exact superpose eq17173 eq12164
    | exact resolve eq12164 eq17173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12164
  have eq17580 : x = (M.op x y) := by grind
  clear eq17514
  have eq17614 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17580 eq20
    | exact resolve eq20 eq17580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq17776 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17614
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17614
    | exact resolve eq17614 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17614
  have eq18171 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17776 eq17318
    | exact resolve eq17318 eq17776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17318
  have eq18200 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18171 eq166
    | exact resolve eq166 eq18171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq18171
  have eq18263 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17580 eq18200
    | exact resolve eq18200 eq17580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18200
  have eq18273 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18263
       have i₂ := eq17173
       grind)
    | exact superpose eq17173 eq18263
    | exact resolve eq18263 eq17173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17173 eq18263
  have eq18280 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17580 eq18273
    | exact resolve eq18273 eq17580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17580 eq18273
  have eq18309 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18280 eq15
    | exact resolve eq15 eq18280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18280
  have eq18366 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18309
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18309
    | exact resolve eq18309 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18309
  have eq18384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17776 eq18366
    | exact resolve eq18366 eq17776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17776 eq18366
  have eq18399 : False := by grind
  exact eq18399

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq46
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq49 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq49
  have eq126 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq131 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq126 X0 X1
       have j1 := eq51 X1 X0
       grind)
    | (have r₁ := eq126 X1 X0
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq126 X1 X1
       have r₂ := eq51 X1 X1
       grind)
    | exact resolve eq126 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq126
  have eq291 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq131 (σ X1) (σ X0)
       grind)
    | exact superpose eq131 eq15
    | exact resolve eq15 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X0 X1
       have i₂ := eq131 X1 X0
       grind)
    | exact superpose eq131 eq291
    | exact resolve eq291 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq291
  have eq300 : False := by grind
  exact eq300

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_x_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq82 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq82
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq82
       grind)
    | exact superpose eq82 eq16
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq147 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (k (k (M.op x y) (M.op x y)) (M.op x y))) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq125 eq41
    | exact resolve eq41 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq201 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq208 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ y)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq500 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq507 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq500 X0
       grind)
    | exact superpose eq500 eq14
    | exact resolve eq14 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq863 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq895 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59 eq507
    | exact resolve eq507 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq897 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq507
    | exact resolve eq507 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq507
  have eq911 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq895 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq924 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq897 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7352 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7351
    | exact resolve eq7351 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7351
  have eq7363 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7352
       have r₂ := eq27
       grind)
    | exact resolve eq7352 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7352
  have eq7365 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7363
    | exact resolve eq7363 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7363
  have eq7367 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7365
    | exact resolve eq7365 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7365
  have eq7369 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7367 eq98
    | (have r₁ := eq98
       have r₂ := eq7367
       grind)
    | exact resolve eq98 eq7367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq7367
  have eq7414 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq7369
  have eq7415 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq7414
  have eq7583 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7415 eq96
    | exact resolve eq96 eq7415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq7415
  have eq7591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7583
  have eq7593 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7591
       have r₂ := eq27
       grind)
    | exact resolve eq7591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7591
  have eq7595 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq7593
       grind)
    | exact superpose eq7593 eq97
    | (have r₁ := eq97
       have r₂ := eq7593
       grind)
    | exact resolve eq97 eq7593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq7613 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq7593
       grind)
    | exact superpose eq7593 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq7593
       grind)
    | exact resolve eq12 eq7593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7593
  have eq7638 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7613
  have eq7639 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7638
  have eq7640 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7595
  have eq7641 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7640
  have eq7663 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq7639
       grind)
    | exact superpose eq7639 eq43
    | exact resolve eq43 eq7639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7639
  have eq7677 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq7663
    | exact resolve eq7663 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7663
  have eq7858 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq7641
       grind)
    | exact superpose eq7641 eq82
    | exact resolve eq82 eq7641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7641
  have eq7872 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq7858
    | exact resolve eq7858 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7858
  have eq8091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7872 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq7872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7872
  have eq8094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8091
    | exact resolve eq8091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8091
  have eq8105 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8094
       have r₂ := eq27
       grind)
    | exact resolve eq8094 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8094
  have eq8107 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8105
    | exact resolve eq8105 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8105
  have eq8109 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8107
    | exact resolve eq8107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8107
  have eq8110 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8109
  have eq8131 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8110 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8110
       grind)
    | exact resolve eq12 eq8110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8110
  have eq8160 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8131
  have eq8161 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8160
  have eq8392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8161 eq7677
    | exact resolve eq7677 eq8161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7677 eq8161
  have eq8394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8392
  have eq8396 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8394
       have r₂ := eq27
       grind)
    | exact resolve eq8394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8394
  have eq8399 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8396 eq51
    | (have r₁ := eq51
       have r₂ := eq8396
       grind)
    | exact resolve eq51 eq8396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq8402 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8396 eq208
    | exact resolve eq208 eq8396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq8428 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8396 eq897
    | exact resolve eq897 eq8396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq8429 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8396 eq924
    | (have r₁ := eq924
       have r₂ := eq8396
       grind)
    | exact resolve eq924 eq8396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq8431 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8429
  have eq8432 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8399
  have eq8952 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8431 eq49
    | exact resolve eq49 eq8431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq8431
  have eq8977 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq8952
    | exact resolve eq8952 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8952
  have eq8986 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8432 eq92
    | exact resolve eq92 eq8432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq8432
  have eq9010 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8986
    | exact resolve eq8986 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8986
  have eq9015 : y = (k y x) := by
    first
    | (have r₁ := eq9010
       have r₂ := eq50
       grind)
    | exact resolve eq9010 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq9010
  have eq9021 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq9015
       grind)
    | exact superpose eq9015 eq82
    | exact resolve eq82 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9015
  have eq9037 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9021
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9021
    | exact resolve eq9021 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9021
  have eq9770 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99 x
       have i₂ := eq8977
       grind)
    | exact superpose eq8977 eq99
    | (have j0 := eq99 x
       grind)
    | exact resolve eq99 eq8977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8977
  have eq9771 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq9770
  have eq10157 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8428 eq8402
    | exact resolve eq8402 eq8428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8402 eq8428
  have eq10199 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10157
  have eq10201 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10199
    | exact resolve eq10199 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10199
  have eq10238 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10201 eq8396
    | exact resolve eq8396 eq10201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8396 eq10201
  have eq10243 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq10238
  have eq10258 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10243 eq29
    | exact resolve eq29 eq10243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10243
  have eq10393 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq10258
    | exact resolve eq10258 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10258
  have eq10406 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq10393 eq20
    | exact resolve eq20 eq10393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10488 : x ≠ x ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq10393 eq911
    | (have r₁ := eq911
       have r₂ := eq10393
       grind)
    | exact resolve eq911 eq10393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq10490 : x = (k x x) ∨ x = y := by grind
  clear eq10488
  have eq10556 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq10406
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10406
    | exact resolve eq10406 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10406
  have eq11041 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq43
       have i₂ := eq10490
       grind)
    | exact superpose eq10490 eq43
    | exact resolve eq43 eq10490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10490
  have eq11063 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11041
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11041
    | exact resolve eq11041 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11041
  have eq11522 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq10556 eq11063
    | exact resolve eq11063 eq10556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10556 eq11063
  have eq11548 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq11522
  have eq12198 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq11548 eq147
    | exact resolve eq147 eq11548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq11548
  have eq12214 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq12198
    | exact resolve eq12198 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12198
  have eq12549 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12214 eq99
    | (have j0 := eq99 (M.op x y)
       grind)
    | exact resolve eq99 eq12214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12214
  have eq12550 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq12549
  have eq12620 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq12550 eq201
    | exact resolve eq201 eq12550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq12550
  have eq13038 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq10393 eq12620
    | exact resolve eq12620 eq10393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12620
  have eq13078 : y = (M.op x y) ∨ x = y := by grind
  clear eq13038
  have eq13079 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13078
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13078
    | exact resolve eq13078 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13078
  have eq13170 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq13079 eq10393
    | exact resolve eq10393 eq13079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10393 eq13079
  have eq13183 : x = y := by grind
  clear eq13170
  have eq13251 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13183
       grind)
    | exact superpose eq13183 eq18
    | exact resolve eq18 eq13183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq13252 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq13183
       grind)
    | exact superpose eq13183 eq24
    | exact resolve eq24 eq13183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq13260 : (σ (k x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq13183
       grind)
    | exact superpose eq13183 eq82
    | exact resolve eq82 eq13183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq13183
  have eq13375 : (σ y) = (σ (k x x)) := by
    first
    | exact superpose eq9037 eq13260
    | exact resolve eq13260 eq9037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9037 eq13260
  have eq13382 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13252
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13252
    | exact resolve eq13252 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13252
  have eq13390 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq13375
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq13375
    | exact resolve eq13375 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq13375
  have eq13705 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13382 eq26
    | exact resolve eq26 eq13382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq13870 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9771
       have i₂ := eq13251
       grind)
    | exact superpose eq13251 eq9771
    | exact resolve eq9771 eq13251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9771 eq13251
  have eq13938 : x = (M.op x y) := by grind
  clear eq13870
  have eq14382 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13938 eq20
    | exact resolve eq20 eq13938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13938
  have eq14554 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14382
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14382
    | exact resolve eq14382 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14382
  have eq14910 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14554 eq13390
    | exact resolve eq13390 eq14554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13390
  have eq14911 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13382 eq14910
    | exact resolve eq14910 eq13382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13382 eq14910
  have eq14912 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14554 eq14911
    | exact resolve eq14911 eq14554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14911
  have eq14947 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14554 eq13705
    | exact resolve eq13705 eq14554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13705 eq14554
  have eq15091 : (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq195 eq863
    | (have j0 := eq863 (M.op x y) (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq863 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq863
  have eq15092 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq15091
    | exact resolve eq15091 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15091
  have eq15224 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq14912 eq15092
    | exact resolve eq15092 eq14912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15092
  have eq15354 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq14912 eq15224
    | exact resolve eq15224 eq14912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15224
  have eq15476 : (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq125 eq15354
    | exact resolve eq15354 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15354
  have eq15590 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq14912 eq15476
    | exact resolve eq15476 eq14912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15476
  have eq15703 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq15590
    | exact resolve eq15590 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15590
  have eq15814 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | (have j1 := eq99 (σ (M.op x y))
       grind)
    | (have r₁ := eq15703
       have r₂ := eq99 (σ (M.op x y))
       grind)
    | exact resolve eq15703 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq15703
  have eq15925 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq14912 eq15814
    | exact resolve eq15814 eq14912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15814
  have eq16032 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq125 eq15925
    | exact resolve eq15925 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq15925
  have eq16129 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14912 eq16032
    | exact resolve eq16032 eq14912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14912 eq16032
  have eq16225 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16129
    | exact resolve eq16129 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq16129
  have eq16226 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq16225
  have eq31585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16226 eq14947
    | exact resolve eq14947 eq16226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14947 eq16226
  have eq31586 : False := by grind
  exact eq31586

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X0 X0) X0 X2
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq62
    | exact resolve eq62 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq77 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  have eq199 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq171 (τ X0)
       grind)
    | exact superpose eq171 eq19
    | (have j1 := eq171 (τ X0)
       grind)
    | exact resolve eq19 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1410 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq389 X1 X0
       grind)
    | exact superpose eq389 eq15
    | (have j1 := eq389 X1 X0
       grind)
    | exact resolve eq15 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7971 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq199 x
       have i₂ := eq405 (τ x) x
       grind)
    | exact superpose eq405 eq199
    | (have j0 := eq199 X0
       have j1 := eq405 (τ X0) X0
       grind)
    | exact resolve eq199 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq405
  have eq8030 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq7971 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7971
  have eq8079 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq8030 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8030
    | (have j0 := eq8030 X0
       grind)
    | exact resolve eq8030 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8030
  have eq8238 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq8079 (τ X0)
       grind)
    | exact superpose eq8079 eq19
    | (have j1 := eq8079 (τ X0)
       grind)
    | exact resolve eq19 eq8079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8079
  have eq8252 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8238 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq8238
    | (have j0 := eq8238 X0
       grind)
    | exact resolve eq8238 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq8238
  have eq8292 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8252 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8252
    | (have j0 := eq8252 X0
       grind)
    | exact resolve eq8252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8252
  have eq8772 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) X1) = X1 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (τ (τ X0)) X1
       have i₂ := eq8292 X0
       grind)
    | exact superpose eq8292 eq77
    | (have j1 := eq8292 X0
       grind)
    | exact resolve eq77 eq8292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8825 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq481 (τ (τ X0)) (τ (τ X0)) x
       have i₂ := eq8292 X0
       grind)
    | exact superpose eq8292 eq481
    | (have j1 := eq8292 X0
       grind)
    | exact resolve eq481 eq8292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8292
  have eq8865 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8825 X0 X1
       have i₂ := eq91 (τ (τ X0)) X1
       grind)
    | exact superpose eq91 eq8825
    | (have j0 := eq8825 X0 X1
       grind)
    | exact resolve eq8825 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8825
  have eq12468 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (τ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq8865 eq8772
    | (have j0 := eq8772 X0 X1
       have j1 := eq8865 X0 X1
       grind)
    | exact resolve eq8772 eq8865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8772
  have eq12643 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | exact superpose eq12468 eq8865
    | (have j0 := eq8865 X0 X1
       have j1 := eq12468 X0 X1
       grind)
    | exact resolve eq8865 eq12468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8865 eq12468
  have eq13986 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq12643 (σ X0) X1
       grind)
    | exact superpose eq12643 eq23
    | (have j1 := eq12643 (σ X0) X1
       grind)
    | exact resolve eq23 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12643
  have eq14034 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13986 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13986
    | (have j0 := eq13986 X0 X1
       grind)
    | exact resolve eq13986 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13986
  have eq14076 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14034 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14034
    | (have j0 := eq14034 X0 X1
       grind)
    | exact resolve eq14034 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14034
  have eq14112 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14076 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14076
    | (have j0 := eq14076 X0 X1
       grind)
    | exact resolve eq14076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14076
  have eq14186 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq14112 (σ X0) X1
       grind)
    | exact superpose eq14112 eq23
    | (have j1 := eq14112 (σ X0) X1
       grind)
    | exact resolve eq23 eq14112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14112
  have eq14234 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14186 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq14186
    | (have j0 := eq14186 X0 X1
       grind)
    | exact resolve eq14186 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14186
  have eq14276 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14234 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14234
    | (have j0 := eq14234 X0 X1
       grind)
    | exact resolve eq14234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14234
  have eq14312 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14276 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14276
    | (have j0 := eq14276 X0 X1
       grind)
    | exact resolve eq14276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14276
  have eq14386 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq14312 (σ X0) X1
       grind)
    | exact superpose eq14312 eq23
    | (have j1 := eq14312 (σ X0) X1
       grind)
    | exact resolve eq23 eq14312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14312
  have eq14434 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14386 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq14386
    | (have j0 := eq14386 X0 X1
       grind)
    | exact resolve eq14386 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14386
  have eq14474 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14434 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14434
    | (have j0 := eq14434 X0 X1
       grind)
    | exact resolve eq14434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14434
  have eq22254 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq171 (σ X0)
       have i₂ := eq1410 X0 X0 X0
       grind)
    | exact superpose eq1410 eq171
    | (have j0 := eq171 (σ X0)
       have j1 := eq1410 X0 X0 x
       grind)
    | exact resolve eq171 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq1410
  have eq22270 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq22254 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22254
  have eq22285 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq14474 eq22270
    | (have j0 := eq22270 X0
       have j1 := eq14474 X0 (σ X0)
       grind)
    | exact resolve eq22270 eq14474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14474 eq22270
  have eq22337 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq22285 (τ X0)
       grind)
    | exact superpose eq22285 eq19
    | (have j1 := eq22285 (τ X0)
       grind)
    | exact resolve eq19 eq22285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22285
  have eq22412 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22337 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22337
    | (have j0 := eq22337 X0
       grind)
    | exact resolve eq22337 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22337
  have eq22431 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq22412 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22412
    | (have j0 := eq22412 X0
       grind)
    | exact resolve eq22412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22412
  have eq22450 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22431 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22431 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22431 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22431
  have eq22532 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22450 (σ X0)
       grind)
    | exact superpose eq22450 eq15
    | exact resolve eq15 eq22450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22592 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22532 X0
       have i₂ := eq22450 X0
       grind)
    | exact superpose eq22450 eq22532
    | exact resolve eq22532 eq22450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22450 eq22532
  have eq22844 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 X1
       have i₂ := eq22592 X1
       grind)
    | exact superpose eq22592 eq389
    | (have j0 := eq389 X0 X1
       grind)
    | exact resolve eq389 eq22592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq22885 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq22592 X0
       grind)
    | exact superpose eq22592 eq9
    | exact resolve eq9 eq22592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22911 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0) (σ X0)
       have i₂ := eq22592 X0
       grind)
    | exact superpose eq22592 eq91
    | exact resolve eq91 eq22592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22992 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22844 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq22844
    | (have j0 := eq22844 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq22844 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22844
  have eq48857 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22992 x y
       grind)
    | exact superpose eq22992 eq16
    | (have j1 := eq22992 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq22992 x y
       grind)
    | exact resolve eq16 eq22992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22992
  have eq49241 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq48857
  have eq94768 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91 (σ x) (σ y)
       have i₂ := eq49241
       grind)
    | exact superpose eq49241 eq91
    | exact resolve eq91 eq49241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94870 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94768
       have i₂ := eq22592 x
       grind)
    | exact superpose eq22592 eq94768
    | exact resolve eq94768 eq22592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94768
  have eq154425 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq94870
       grind)
    | exact superpose eq94870 eq10
    | exact resolve eq10 eq94870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94870
  have eq154694 : y = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq154425
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq154425
    | exact resolve eq154425 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154425
  have eq154695 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq154694
  have eq154700 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq154695 eq49241
    | exact resolve eq49241 eq154695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49241
  have eq154791 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq154695
       grind)
    | exact superpose eq154695 eq10
    | exact resolve eq10 eq154695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154695
  have eq155062 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq154791
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq154791
    | exact resolve eq154791 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154791
  have eq155246 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22911 x
       have i₂ := eq155062
       grind)
    | exact superpose eq155062 eq22911
    | exact resolve eq22911 eq155062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155441 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91 x x
       have i₂ := eq155062
       grind)
    | exact superpose eq155062 eq91
    | exact resolve eq91 eq155062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155062
  have eq156621 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq155246
       grind)
    | exact superpose eq155246 eq16
    | exact resolve eq16 eq155246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155246
  have eq156860 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq155441 eq156621
    | exact resolve eq156621 eq155441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155441 eq156621
  have eq156861 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq156860
  have eq156985 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq91 x y
       have i₂ := eq156861
       grind)
    | exact superpose eq156861 eq91
    | exact resolve eq91 eq156861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156861
  have eq157103 : x = (M.op x x) := by grind
  clear eq156985
  have eq157280 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq77 x X0
       have i₂ := eq157103
       grind)
    | exact superpose eq157103 eq77
    | exact resolve eq77 eq157103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq157618 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq481 x x x
       have i₂ := eq157103
       grind)
    | exact superpose eq157103 eq481
    | exact resolve eq481 eq157103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq157755 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq157618 X0
       have i₂ := eq91 x X0
       grind)
    | exact superpose eq91 eq157618
    | exact resolve eq157618 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq157618
  have eq157928 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq154700
       have i₂ := eq157103
       grind)
    | exact superpose eq157103 eq154700
    | exact resolve eq154700 eq157103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154700 eq157103
  have eq158653 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq157280 X0
       have i₂ := eq157755 X0
       grind)
    | exact superpose eq157755 eq157280
    | exact resolve eq157280 eq157755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157280
  have eq158654 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq158653 y
       grind)
    | exact superpose eq158653 eq16
    | exact resolve eq16 eq158653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158655 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq157928
       have i₂ := eq158653 y
       grind)
    | exact superpose eq158653 eq157928
    | exact resolve eq157928 eq158653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157928
  have eq158656 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq157755 X0
       have i₂ := eq158653 X0
       grind)
    | exact superpose eq158653 eq157755
    | exact resolve eq157755 eq158653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157755 eq158653
  have eq159315 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq158655
  have eq162908 : (σ y) = (M.op (M.op (σ x) (σ (M.op x x))) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22885 x (σ y)
       have i₂ := eq159315
       grind)
    | exact superpose eq159315 eq22885
    | exact resolve eq22885 eq159315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22885 eq159315
  have eq163088 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq162908
       have i₂ := eq22911 x
       grind)
    | exact superpose eq22911 eq162908
    | exact resolve eq162908 eq22911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22911 eq162908
  have eq163137 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq163088
       have i₂ := eq158656 x
       grind)
    | exact superpose eq158656 eq163088
    | exact resolve eq163088 eq158656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163088
  have eq163156 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq163137
       have r₂ := eq158654
       grind)
    | exact resolve eq163137 eq158654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163137
  have eq163171 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq163156
  have eq164001 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq163171
  have eq164967 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq164001
       grind)
    | exact superpose eq164001 eq10
    | exact resolve eq10 eq164001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164001
  have eq165199 : x = y ∨ x = y := by
    first
    | (have i₁ := eq164967
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq164967
    | exact resolve eq164967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164967
  have eq165200 : x = y := by grind
  clear eq165199
  have eq165206 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq158654
       have i₂ := eq165200
       grind)
    | exact superpose eq165200 eq158654
    | exact resolve eq158654 eq165200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158654 eq165200
  have eq165207 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq165206
       have i₂ := eq22592 x
       grind)
    | exact superpose eq22592 eq165206
    | exact resolve eq165206 eq22592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22592 eq165206
  have eq165208 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq165207
       have i₂ := eq158656 x
       grind)
    | exact superpose eq158656 eq165207
    | exact resolve eq165207 eq158656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158656 eq165207
  have eq165209 : False := by grind
  exact eq165209
