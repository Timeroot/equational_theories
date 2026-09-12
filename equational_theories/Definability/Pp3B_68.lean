import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4294`: `x ◇ (x ◇ y) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pxy_Equation4294 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4294 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4294.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X1 X2)) := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op x (M.op x y)) := by
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
  have eq180 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X3 X0)
       have i₂ := eq16 X3 X0 X1
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X1 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq179 X1
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) X1)) := by
    intro X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq201 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | (have i₁ := eq198 x X1
       have i₂ := eq190 x X1
       grind)
    | (have i₁ := eq198 x y
       have i₂ := eq190 x X1
       grind)
    | exact superpose eq190 eq198
    | exact resolve eq198 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq197 x
       have i₂ := eq190 sF2 x
       grind)
    | exact superpose eq190 eq197
    | (have j1 := eq190 (σ x) (σ y)
       grind)
    | exact resolve eq197 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq212 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq190 X0 (M.op X0 x)
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq190
    | exact resolve eq190 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq223 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq202 eq212
    | exact resolve eq212 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq287 : (M.op x (M.op x y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (M.op x y))) := by
    first
    | exact superpose eq201 eq174
    | exact resolve eq174 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq297 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq202 eq287
    | exact resolve eq287 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq300 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq311 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1212 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1225 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1226 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1328 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1226 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1226
    | (have j0 := eq1226 (σ X0)
       grind)
    | exact resolve eq1226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2576 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1212
       grind)
    | exact superpose eq1212 eq40
    | exact resolve eq40 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2577 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2576
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2576
    | exact resolve eq2576 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2576
  have eq2579 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2577
    | exact resolve eq2577 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq17851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2579 eq1218
    | exact resolve eq1218 eq2579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq17858 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17851
       have r₂ := eq27
       grind)
    | exact resolve eq17851 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17851
  have eq17865 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17858 eq311
    | exact resolve eq311 eq17858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq17858
  have eq17888 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17865
    | exact resolve eq17865 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17865
  have eq17897 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq17888
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq17888
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq17888
       have r₂ := eq13 x y
       grind)
    | exact resolve eq17888 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17888
  have eq17906 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17897 eq300
    | exact resolve eq300 eq17897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq17897
  have eq17932 : y = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17906
    | exact resolve eq17906 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17906
  have eq17939 : y = (k y y) ∨ y = (k x y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq17932
       have r₂ := eq13 x y
       grind)
    | exact resolve eq17932 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17932
  have eq17950 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1328 y
       have i₂ := eq17939
       grind)
    | exact superpose eq17939 eq1328
    | (have j0 := eq1328 y
       grind)
    | exact resolve eq1328 eq17939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17954 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1226 y
       have i₂ := eq17939
       grind)
    | exact superpose eq17939 eq1226
    | (have j0 := eq1226 y
       grind)
    | (have r₁ := eq1226 y
       have r₂ := eq17939
       grind)
    | exact resolve eq1226 eq17939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq17939
  have eq17955 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq17954
  have eq17957 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by grind
  clear eq17950
  have eq17958 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq17957
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17957
    | exact resolve eq17957 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17957
  have eq17966 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1212
       have i₂ := eq17955
       grind)
    | exact superpose eq17955 eq1212
    | exact resolve eq1212 eq17955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq17955
  have eq17969 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq17966
  have eq17989 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq17958 eq196
    | exact resolve eq196 eq17958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17992 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq17958 eq17989
    | exact resolve eq17989 eq17958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17958 eq17989
  have eq18066 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (k x y) := by
    first
    | exact superpose eq17992 eq190
    | exact resolve eq190 eq17992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18068 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq202 eq18066
    | exact resolve eq18066 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18066
  have eq18077 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq18068
    | exact resolve eq18068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18068
  have eq18085 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17992 eq18077
    | exact resolve eq18077 eq17992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17992 eq18077
  have eq18100 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq18085
       grind)
    | exact superpose eq18085 eq35
    | exact resolve eq35 eq18085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq18085
  have eq18103 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18100
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18100
    | exact resolve eq18100 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18100
  have eq18112 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18103 eq1218
    | exact resolve eq1218 eq18103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218 eq18103
  have eq18116 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq18112
  have eq18209 : y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq17969
       grind)
    | exact superpose eq17969 eq174
    | exact resolve eq174 eq17969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq18220 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq196 y y
       have i₂ := eq17969
       grind)
    | exact superpose eq17969 eq196
    | exact resolve eq196 eq17969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18223 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17969 eq18220
    | exact resolve eq18220 eq17969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17969 eq18220
  have eq18513 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1328 y
       have i₂ := eq18209
       grind)
    | exact superpose eq18209 eq1328
    | (have j0 := eq1328 y
       grind)
    | exact resolve eq1328 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18209
  have eq18520 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq18513
  have eq18522 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18520
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18520
    | exact resolve eq18520 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18520
  have eq19100 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq18522 eq182
    | exact resolve eq182 eq18522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq19104 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18522 eq196
    | exact resolve eq196 eq18522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19107 : y = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18223 eq19104
    | exact resolve eq19104 eq18223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19104
  have eq19111 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq19100 x X1
       have i₂ := eq190 x X1
       grind)
    | (have i₁ := eq19100 x y
       have i₂ := eq190 x X1
       grind)
    | exact superpose eq190 eq19100
    | exact resolve eq19100 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19100
  have eq19117 : y = (M.op x x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq18522 eq19107
    | exact resolve eq19107 eq18522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19107
  have eq19121 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq202 eq19111
    | exact resolve eq19111 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19111
  have eq19128 : ∀ X1 : G, y = (M.op X1 (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq18223 eq19121
    | exact resolve eq19121 eq18223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18223 eq19121
  have eq19134 : ∀ X1 : G, y = (M.op X1 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq18522 eq19128
    | exact resolve eq19128 eq18522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18522 eq19128
  have eq19137 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq19117 eq19134
    | exact resolve eq19134 eq19117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19134
  have eq19156 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq196 x x
       have i₂ := eq19117
       grind)
    | exact superpose eq19117 eq196
    | exact resolve eq196 eq19117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19117
  have eq19159 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq19156
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19156
    | exact resolve eq19156 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19156
  have eq19195 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq19159 eq297
    | exact resolve eq297 eq19159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19329 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq19195 eq1328
    | (have j0 := eq1328 (M.op x y)
       grind)
    | exact resolve eq1328 eq19195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19195
  have eq19336 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq19329
  have eq19337 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq19336
    | exact resolve eq19336 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19336
  have eq19380 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq19337 eq196
    | exact resolve eq196 eq19337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19383 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq19159 eq19380
    | exact resolve eq19380 eq19159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19380
  have eq19413 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq19383 eq19337
    | exact resolve eq19337 eq19383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19337 eq19383
  have eq19430 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq19413
  have eq19887 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18116 eq196
    | exact resolve eq196 eq18116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19890 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18116 eq19887
    | exact resolve eq19887 eq18116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18116 eq19887
  have eq20987 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19137 eq26
    | (have j1 := eq19137 (σ x)
       grind)
    | exact resolve eq26 eq19137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21079 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq196 x x
       have i₂ := eq20987
       grind)
    | exact superpose eq20987 eq196
    | exact resolve eq196 eq20987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20987
  have eq21082 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21079
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21079
    | exact resolve eq21079 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21079
  have eq21118 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21082 eq297
    | exact resolve eq297 eq21082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21255 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21118 eq1328
    | (have j0 := eq1328 (M.op x y)
       grind)
    | exact resolve eq1328 eq21118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21118
  have eq21259 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21255
  have eq21264 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq21259
    | exact resolve eq21259 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21259
  have eq21321 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21264 eq196
    | exact resolve eq196 eq21264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21329 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21082 eq21321
    | exact resolve eq21321 eq21082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21321
  have eq21365 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21329 eq21264
    | exact resolve eq21264 eq21329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21264 eq21329
  have eq21381 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq21365
  have eq21416 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21381 eq223
    | exact resolve eq223 eq21381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq21435 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26 eq21416
    | (have j0 := eq21416 X0
       grind)
    | exact resolve eq21416 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21416
  have eq21444 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21381 eq21435
    | exact resolve eq21435 eq21381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21381 eq21435
  have eq22396 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19890 eq190
    | exact resolve eq190 eq19890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq22400 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq202 eq22396
    | exact resolve eq22396 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22396
  have eq22415 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq22400
    | exact resolve eq22400 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22400
  have eq22423 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19890 eq22415
    | exact resolve eq22415 eq19890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19890 eq22415
  have eq22424 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22423
  have eq22446 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22424 eq196
    | exact resolve eq196 eq22424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22424
  have eq22449 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22446
    | exact resolve eq22446 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22446
  have eq22493 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22449 eq21082
    | exact resolve eq21082 eq22449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21082 eq22449
  have eq22503 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq22493
  have eq22667 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22503 eq19159
    | exact resolve eq19159 eq22503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19159
  have eq22670 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq22667
  have eq22675 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22670
    | exact resolve eq22670 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22670
  have eq22676 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq22675
  have eq22716 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq22676 eq27
    | exact resolve eq27 eq22676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22676
  have eq22750 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22716
       have r₂ := eq19430
       grind)
    | exact resolve eq22716 eq19430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19430 eq22716
  have eq22754 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22750
       grind)
    | exact superpose eq22750 eq18
    | exact resolve eq18 eq22750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22785 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  have eq22979 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22754 eq21444
    | exact resolve eq21444 eq22754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21444
  have eq22980 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22754 eq19137
    | exact resolve eq19137 eq22754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19137
  have eq22992 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq22980
  have eq22993 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq22979
  have eq23004 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22992
       have r₂ := eq22785
       grind)
    | exact resolve eq22992 eq22785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22992
  have eq23005 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22993
       have r₂ := eq22785
       grind)
    | exact resolve eq22993 eq22785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22785 eq22993
  have eq23014 : (σ y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22750 eq23004
    | exact resolve eq23004 eq22750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22750 eq23004
  have eq23283 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq196 x x
       have i₂ := eq23014
       grind)
    | exact superpose eq23014 eq196
    | exact resolve eq196 eq23014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23014
  have eq23294 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22754 eq23283
    | exact resolve eq23283 eq22754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22754 eq23283
  have eq23384 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22503 eq23294
    | exact resolve eq23294 eq22503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22503 eq23294
  have eq23418 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq23384
  have eq23438 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23418
    | exact resolve eq23418 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23418
  have eq23439 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23438
  have eq23465 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23439 eq27
    | exact resolve eq27 eq23439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23439
  have eq23503 : y = (M.op x y) := by
    first
    | (have r₁ := eq23465
       have r₂ := eq23005
       grind)
    | exact resolve eq23465 eq23005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23005 eq23465
  have eq23512 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23503
       grind)
    | exact superpose eq23503 eq18
    | exact resolve eq18 eq23503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq23513 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq23503
       grind)
    | exact superpose eq23503 eq24
    | exact resolve eq24 eq23503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq23503
  have eq23549 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23513 eq20
    | exact resolve eq20 eq23513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23513
  have eq24583 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq23512 eq202
    | exact resolve eq202 eq23512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq23512
  have eq24615 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq24583 eq297
    | exact resolve eq297 eq24583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq24630 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq24583 eq196
    | exact resolve eq196 eq24583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24749 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24615 eq1328
    | (have j0 := eq1328 (M.op x y)
       grind)
    | exact resolve eq1328 eq24615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq24615
  have eq24753 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq24749
  have eq24758 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq24753
    | exact resolve eq24753 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq24753
  have eq24765 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq23549 eq24758
    | exact resolve eq24758 eq23549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24758
  have eq24844 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq24765 eq196
    | exact resolve eq196 eq24765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq24847 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq24765 eq24844
    | exact resolve eq24844 eq24765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24765 eq24844
  have eq24856 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq24583 eq24847
    | exact resolve eq24847 eq24583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24583 eq24847
  have eq24870 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq24856 eq26
    | exact resolve eq26 eq24856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq25017 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24630 eq24870
    | exact resolve eq24870 eq24630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24630 eq24870
  have eq25100 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq25017 eq27
    | exact resolve eq27 eq25017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25017
  have eq25127 : (M.op x y) ≠ (σ y) := by
    first
    | exact superpose eq23549 eq25100
    | exact resolve eq25100 eq23549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23549 eq25100
  have eq25130 : False := by grind
  exact eq25130

/-- `Equation4294`: `x ◇ (x ◇ y) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4294 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4294 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4294.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X1 X2)) := by
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
  have eq55 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op x (M.op x y)) := by
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
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq121 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq215 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1
       have i₂ := eq14 X0 X1 x
       grind)
    | (have i₁ := eq55 X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq358 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq215
    | (have j0 := eq215 (σ x) (σ y)
       grind)
    | exact resolve eq215 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq215 X0 (M.op X0 x)
       have i₂ := eq215 X0 x
       grind)
    | (have i₁ := eq215 x (M.op x y)
       have i₂ := eq215 X0 x
       grind)
    | exact superpose eq215 eq215
    | exact resolve eq215 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq359 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq359 X0
       grind)
    | exact resolve eq13 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq800 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq811 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq800 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq800 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq800 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq800 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq828 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq811 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq811
    | (have j0 := eq811 X0 X1
       grind)
    | exact resolve eq811 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq3355 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq84 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq84
    | (have j0 := eq84 x
       grind)
    | exact resolve eq84 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq3363 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3355
  have eq3369 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3363
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3363
    | exact resolve eq3363 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3363
  have eq3387 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3369
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3369 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq3392 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3387 eq50
    | exact resolve eq50 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq3387
  have eq6536 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq828 X0 (M.op X0 X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq828
    | (have j0 := eq828 X0 (M.op X0 X0)
       grind)
    | exact resolve eq828 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq828
  have eq6654 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536
  have eq6655 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6654 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6654
  have eq7200 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6655 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6655
    | exact resolve eq6655 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7282 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6655 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6655
    | (have j0 := eq6655 x
       grind)
    | exact resolve eq6655 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7291 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq215 (σ X0) (σ X0)
       have i₂ := eq6655 X0
       grind)
    | exact superpose eq6655 eq215
    | exact resolve eq215 eq6655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655
  have eq7490 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq7282
       grind)
    | exact superpose eq7282 eq16
    | exact resolve eq16 eq7282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7282
  have eq7517 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq3392 eq7490
    | exact resolve eq7490 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7490
  have eq8600 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq7200 X0
       grind)
    | exact superpose eq7200 eq16
    | exact resolve eq16 eq7200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7200
  have eq8760 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8600 X0
       have i₂ := eq452 (τ X0)
       grind)
    | exact superpose eq452 eq8600
    | exact resolve eq8600 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8768 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq215 (τ X0) (τ X0)
       have i₂ := eq8600 X0
       grind)
    | exact superpose eq8600 eq215
    | exact resolve eq215 eq8600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8600
  have eq10788 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq359 eq8768
    | exact resolve eq8768 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8768
  have eq10815 : (M.op x (M.op x y)) = (k (τ (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq10788
       have i₂ := eq452 (τ (M.op x sF0))
       grind)
    | exact superpose eq452 eq10788
    | exact resolve eq10788 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq10788
  have eq10864 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | exact superpose eq8760 eq10815
    | exact resolve eq10815 eq8760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8760 eq10815
  have eq10905 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq359 eq10864
    | exact resolve eq10864 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10864
  have eq10907 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq10905 eq15
    | exact resolve eq15 eq10905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq14186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14185
    | exact resolve eq14185 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14185
  have eq14199 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14186
       have r₂ := eq28
       grind)
    | exact resolve eq14186 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14186
  have eq14204 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14199
    | exact resolve eq14199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14199
  have eq14206 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14204 eq3392
    | exact resolve eq3392 eq14204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392 eq14204
  have eq14222 : (τ (σ y)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14206
       have i₂ := eq7517
       grind)
    | exact superpose eq7517 eq14206
    | exact resolve eq14206 eq7517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7517 eq14206
  have eq14227 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq14222
    | exact resolve eq14222 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14222
  have eq14228 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14227
  have eq14234 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7291 x
       have i₂ := eq14228
       grind)
    | exact superpose eq14228 eq7291
    | exact resolve eq7291 eq14228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7291
  have eq14236 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq215 x x
       have i₂ := eq14228
       grind)
    | exact superpose eq14228 eq215
    | exact resolve eq215 eq14228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq14228
  have eq14243 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14236
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14236
    | exact resolve eq14236 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14236
  have eq14244 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14234
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14234
    | exact resolve eq14234 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14234
  have eq14249 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14244
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14244
    | exact resolve eq14244 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14244
  have eq14250 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14249
    | exact resolve eq14249 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14249
  have eq14504 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14243 eq10907
    | exact resolve eq10907 eq14243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14511 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq14504
    | exact resolve eq14504 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14504
  have eq14515 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14511 eq358
    | exact resolve eq358 eq14511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14518 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14515
    | exact resolve eq14515 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14515
  have eq14803 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14250 eq14243
    | exact resolve eq14243 eq14250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14243 eq14250
  have eq14809 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14803
  have eq14816 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14809 eq358
    | exact resolve eq358 eq14809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq14818 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq14820 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14816
    | exact resolve eq14816 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14816
  have eq15960 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14820 eq359
    | exact resolve eq359 eq14820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15971 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14820 eq10905
    | exact resolve eq10905 eq14820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14820
  have eq15986 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14809 eq15971
    | exact resolve eq15971 eq14809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15971
  have eq16022 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq15986
  have eq16025 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16022
       have r₂ := eq14818
       grind)
    | exact resolve eq16022 eq14818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16022
  have eq16026 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq16025
    | exact resolve eq16025 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16025
  have eq16029 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq16026 eq28
    | exact resolve eq28 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16026
  have eq16420 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14809 eq15960
    | exact resolve eq15960 eq14809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14809 eq15960
  have eq16434 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq16420 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16420
  have eq16440 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq16434 X0
       grind)
    | (have r₁ := eq16434 X0
       have r₂ := eq14818
       grind)
    | exact resolve eq16434 eq14818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14818 eq16434
  have eq16454 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14518 eq10905
    | exact resolve eq10905 eq14518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10905
  have eq16455 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14518 eq10907
    | exact resolve eq10907 eq14518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14518
  have eq16472 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14511 eq16454
    | exact resolve eq16454 eq14511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14511 eq16454
  have eq16506 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq16472
  have eq16510 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq16506
    | exact resolve eq16506 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16506
  have eq16513 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16510
       have r₂ := eq16029
       grind)
    | exact resolve eq16510 eq16029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16029 eq16510
  have eq16871 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16513 eq16440
    | exact resolve eq16440 eq16513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16440 eq16513
  have eq16889 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq16871 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16871
  have eq17275 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq16889 x
       grind)
    | exact superpose eq16889 eq19
    | (have j1 := eq16889 x
       grind)
    | exact resolve eq19 eq16889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16889
  have eq17281 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17275
  have eq17294 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17281 eq28
    | exact resolve eq28 eq17281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17304 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17281 eq16455
    | exact resolve eq16455 eq17281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16455 eq17281
  have eq17307 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq17304
  have eq17318 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq17307
    | exact resolve eq17307 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17307
  have eq17319 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq17318
  have eq17323 : y = (M.op x y) := by
    first
    | (have r₁ := eq17319
       have r₂ := eq17294
       grind)
    | exact resolve eq17319 eq17294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17294 eq17319
  have eq17325 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17323 eq21
    | exact resolve eq21 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17376 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17323 eq359
    | exact resolve eq359 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq17392 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17323 eq10907
    | exact resolve eq10907 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10907
  have eq17394 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq17392
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17392
    | exact resolve eq17392 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17392
  have eq17408 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq17376 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17376
    | (have j0 := eq17376 X0
       grind)
    | exact resolve eq17376 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17376
  have eq17458 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq17325
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17325
    | exact resolve eq17325 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17325
  have eq17459 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq17394
    | exact resolve eq17394 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17394
  have eq17471 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq17323 eq17408
    | exact resolve eq17408 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17408
  have eq17497 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq17323 eq17459
    | exact resolve eq17459 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17323 eq17459
  have eq17518 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17458 eq27
    | exact resolve eq27 eq17458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17458
  have eq18030 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq17497 eq17518
    | exact resolve eq17518 eq17497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17518
  have eq18031 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18030
       have i₂ := eq17471 sF2
       grind)
    | exact superpose eq17471 eq18030
    | exact resolve eq18030 eq17471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17471 eq18030
  have eq18036 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq18031 eq28
    | exact resolve eq28 eq18031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18031
  have eq18066 : False := by grind
  exact eq18066

/-- `Equation4308`: `x ◇ (x ◇ y) = z ◇ (z ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_y_pxx_pxy_Equation4308 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4308 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4308.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq79
    | exact resolve eq79 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq216 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (σ x) (σ y)
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq47 X0 (M.op X0 x)
       have i₂ := eq47 X0 x
       grind)
    | (have i₁ := eq47 x (M.op x y)
       have i₂ := eq47 X0 x
       grind)
    | exact superpose eq47 eq47
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq71 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq71 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq71 X1 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq837 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq831 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq841 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq837 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq837 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq837 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq837 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq852 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq841
    | (have j0 := eq841 X0 X1
       grind)
    | exact resolve eq841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq6307 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq852
  have eq6421 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6307 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6307
  have eq6422 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6421
  have eq6864 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6422 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6422
    | (have j0 := eq6422 x
       grind)
    | exact resolve eq6422 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6872 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq47 (σ X0) (σ X0)
       have i₂ := eq6422 X0
       grind)
    | exact superpose eq6422 eq47
    | exact resolve eq47 eq6422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6890 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq6864
       grind)
    | exact superpose eq6864 eq16
    | exact resolve eq16 eq6864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6864
  have eq8031 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq217 eq6872
    | exact resolve eq6872 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8063 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq8031
       have i₂ := eq6422 (M.op x sF0)
       grind)
    | exact superpose eq6422 eq8031
    | exact resolve eq8031 eq6422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6422 eq8031
  have eq8077 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq217 eq8063
    | exact resolve eq8063 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8063
  have eq8084 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq8077 eq16
    | exact resolve eq16 eq8077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq10876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10875
    | exact resolve eq10875 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10875
  have eq10889 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10876
       have r₂ := eq28
       grind)
    | exact resolve eq10876 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10876
  have eq10892 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10889
    | exact resolve eq10889 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10889
  have eq10894 : (τ (σ y)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10892 eq6890
    | exact resolve eq6890 eq10892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6890 eq10892
  have eq10906 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq10894
    | exact resolve eq10894 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10894
  have eq10907 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10906
  have eq10914 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6872 x
       have i₂ := eq10907
       grind)
    | exact superpose eq10907 eq6872
    | exact resolve eq6872 eq10907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6872
  have eq10916 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47 x x
       have i₂ := eq10907
       grind)
    | exact superpose eq10907 eq47
    | exact resolve eq47 eq10907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq10907
  have eq10922 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10916
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10916
    | exact resolve eq10916 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10916
  have eq10923 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10914
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10914
    | exact resolve eq10914 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10914
  have eq10927 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10923
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10923
    | exact resolve eq10923 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10923
  have eq10928 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq10927
    | exact resolve eq10927 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10927
  have eq11123 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10922 eq8077
    | exact resolve eq8077 eq10922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11132 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq11123
    | exact resolve eq11123 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11123
  have eq11134 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11132 eq216
    | exact resolve eq216 eq11132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11137 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11134
    | exact resolve eq11134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11134
  have eq11475 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10928 eq10922
    | exact resolve eq10922 eq10928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10922 eq10928
  have eq11482 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11475
  have eq11488 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11482 eq216
    | exact resolve eq216 eq11482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq11490 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq11492 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11488
    | exact resolve eq11488 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11488
  have eq12449 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11137 eq217
    | exact resolve eq217 eq11137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12456 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11137 eq8084
    | exact resolve eq8084 eq11137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11137
  have eq12532 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11132 eq12456
    | exact resolve eq12456 eq11132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12456
  have eq12565 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq12532
  have eq12567 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq12565
    | exact resolve eq12565 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12565
  have eq13006 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11492 eq217
    | exact resolve eq217 eq11492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13013 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11492 eq8084
    | exact resolve eq8084 eq11492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8084 eq11492
  have eq13233 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11482 eq13013
    | exact resolve eq13013 eq11482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13013
  have eq13268 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq13233
  have eq13270 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13268
       have r₂ := eq11490
       grind)
    | exact resolve eq13268 eq11490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13268
  have eq13271 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq13270
    | exact resolve eq13270 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13270
  have eq13274 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq13271 eq28
    | exact resolve eq28 eq13271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13271
  have eq13294 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13274
       have r₂ := eq12567
       grind)
    | exact resolve eq13274 eq12567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12567 eq13274
  have eq13827 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11132 eq12449
    | exact resolve eq12449 eq11132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11132 eq12449
  have eq13839 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13827 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13827
  have eq13882 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11482 eq13006
    | exact resolve eq13006 eq11482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11482 eq13006
  have eq13896 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq13882 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13882
  have eq13902 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq13896 X0
       grind)
    | (have r₁ := eq13896 X0
       have r₂ := eq11490
       grind)
    | exact resolve eq13896 eq11490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11490 eq13896
  have eq13938 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13294 eq13839
    | exact resolve eq13839 eq13294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13839
  have eq13956 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13938
  have eq14024 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13294 eq13902
    | exact resolve eq13902 eq13294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13294 eq13902
  have eq14042 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14024
  have eq14632 : y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq13956 x
       grind)
    | exact superpose eq13956 eq19
    | (have j1 := eq13956 x
       grind)
    | exact resolve eq19 eq13956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13956
  have eq14638 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq14632
  have eq15421 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14042 x
       grind)
    | exact superpose eq14042 eq19
    | (have j1 := eq14042 x
       grind)
    | exact resolve eq19 eq14042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14042
  have eq15427 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15421
  have eq15439 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15427 eq28
    | exact resolve eq28 eq15427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15427
  have eq15463 : y = (M.op x y) := by
    first
    | (have r₁ := eq15439
       have r₂ := eq14638
       grind)
    | exact resolve eq15439 eq14638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14638 eq15439
  have eq15464 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq15463 eq21
    | exact resolve eq21 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15510 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq15463 eq217
    | exact resolve eq217 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq15524 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq15463 eq8077
    | exact resolve eq8077 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8077
  have eq15528 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq15524
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15524
    | exact resolve eq15524 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15524
  have eq15542 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq15510 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15510
    | (have j0 := eq15510 X0
       grind)
    | exact resolve eq15510 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15510
  have eq15587 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15464
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15464
    | exact resolve eq15464 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15464
  have eq15589 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq15528
    | exact resolve eq15528 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq15528
  have eq15595 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq15463 eq15542
    | exact resolve eq15542 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15542
  have eq15596 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq15463 eq15589
    | exact resolve eq15589 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15463 eq15589
  have eq15800 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq15587 eq27
    | exact resolve eq27 eq15587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15587
  have eq16431 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq15596 eq15800
    | exact resolve eq15800 eq15596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15800
  have eq16432 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16431
       have i₂ := eq15595 sF2
       grind)
    | exact superpose eq15595 eq16431
    | exact resolve eq16431 eq15595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15595 eq16431
  have eq16437 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq16432 eq28
    | exact resolve eq28 eq16432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16432
  have eq16467 : False := by grind
  exact eq16467

/-- `Equation4311`: `x ◇ (x ◇ y) = z ◇ (w ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4311 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4311 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4311.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq86 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq123 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq217 : (M.op x (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq51 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y x
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op x X0) X2 X3
       have i₂ := eq51 X0 x
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq228 X0 x x
       have i₂ := eq51 x x
       grind)
    | exact superpose eq51 eq228
    | exact resolve eq228 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq231 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq51 x x
       grind)
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq247 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq217 eq57
    | exact resolve eq57 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq217
  have eq404 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq229 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq229 X0
       grind)
    | exact resolve eq13 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq404 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq768 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq85 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq785 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq768 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq768 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq768 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq768 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq797 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq785 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq785
    | (have j0 := eq785 X0 X1
       grind)
    | exact resolve eq785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq3408 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq86 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq86
    | (have j0 := eq86 x
       grind)
    | exact resolve eq86 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq3419 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3408
  have eq3427 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3419
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3419
    | exact resolve eq3419 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3419
  have eq3444 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3427
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3427 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3427
  have eq3449 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3444 eq50
    | exact resolve eq50 eq3444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq3444
  have eq6371 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq797 X0 (M.op X0 X0)
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq797
    | (have j0 := eq797 X0 (M.op X0 X0)
       grind)
    | exact resolve eq797 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq797
  have eq6489 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6371
  have eq6490 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6489 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6489
  have eq7117 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6490 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6490
    | (have j0 := eq6490 x
       grind)
    | exact resolve eq6490 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7121 : ∀ X0 : G, (k (σ X0) (M.op x (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6490 X0
       have i₂ := eq408 (σ X0)
       grind)
    | exact superpose eq408 eq6490
    | exact resolve eq6490 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7128 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0) (σ X0)
       have i₂ := eq6490 X0
       grind)
    | exact superpose eq6490 eq51
    | exact resolve eq51 eq6490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq6490
  have eq7328 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq7117
       grind)
    | exact superpose eq7117 eq16
    | exact resolve eq16 eq7117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7117
  have eq7355 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq3449 eq7328
    | exact resolve eq7328 eq3449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7328
  have eq10043 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq229 eq7128
    | exact resolve eq7128 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10083 : (M.op x (M.op x y)) = (k (σ (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq10043
       have i₂ := eq408 (σ (M.op x sF0))
       grind)
    | exact superpose eq408 eq10043
    | exact resolve eq10043 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq10043
  have eq10170 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | exact superpose eq7121 eq10083
    | exact resolve eq10083 eq7121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7121 eq10083
  have eq10248 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq229 eq10170
    | exact resolve eq10170 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10170
  have eq10253 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq10248 eq16
    | exact resolve eq16 eq10248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq15975 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15966
    | exact resolve eq15966 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15966
  have eq15987 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15975
       have r₂ := eq28
       grind)
    | exact resolve eq15975 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15975
  have eq15991 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15987
    | exact resolve eq15987 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15987
  have eq15993 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15991 eq3449
    | exact resolve eq3449 eq15991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449 eq15991
  have eq16010 : (τ (σ y)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15993
       have i₂ := eq7355
       grind)
    | exact superpose eq7355 eq15993
    | exact resolve eq15993 eq7355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7355 eq15993
  have eq16014 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq16010
    | exact resolve eq16010 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16010
  have eq16015 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16014
  have eq16019 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7128 x
       have i₂ := eq16015
       grind)
    | exact superpose eq16015 eq7128
    | exact resolve eq7128 eq16015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7128
  have eq16025 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq247 x x
       have i₂ := eq16015
       grind)
    | exact superpose eq16015 eq247
    | exact resolve eq247 eq16015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq16015
  have eq16026 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16025
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16025
    | exact resolve eq16025 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16025
  have eq16031 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16019
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16019
    | exact resolve eq16019 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16019
  have eq16035 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16031
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16031
    | exact resolve eq16031 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16031
  have eq16036 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq16035
    | exact resolve eq16035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16035
  have eq16309 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16026 eq10248
    | exact resolve eq10248 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16323 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq16309
    | exact resolve eq16309 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16309
  have eq16328 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16323 eq231
    | exact resolve eq231 eq16323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16331 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq16328
    | exact resolve eq16328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16328
  have eq16622 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16036 eq16026
    | exact resolve eq16026 eq16036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16026 eq16036
  have eq16632 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16622
  have eq16642 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16632 eq231
    | exact resolve eq231 eq16632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq16644 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq16646 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq16642
    | exact resolve eq16642 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16642
  have eq17826 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16331 eq229
    | exact resolve eq229 eq16331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17841 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16331 eq10253
    | exact resolve eq10253 eq16331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16331
  have eq18128 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16323 eq17841
    | exact resolve eq17841 eq16323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17841
  have eq18162 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq18128
  have eq18165 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq18162
    | exact resolve eq18162 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18162
  have eq18333 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16646 eq229
    | exact resolve eq229 eq16646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18348 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16646 eq10253
    | exact resolve eq10253 eq16646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10253 eq16646
  have eq18431 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16632 eq18348
    | exact resolve eq18348 eq16632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18348
  have eq18467 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq18431
  have eq18470 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18467
       have r₂ := eq16644
       grind)
    | exact resolve eq18467 eq16644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18467
  have eq18471 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq18470
    | exact resolve eq18470 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18470
  have eq18475 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq18471 eq28
    | exact resolve eq28 eq18471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18471
  have eq18494 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18475
       have r₂ := eq18165
       grind)
    | exact resolve eq18475 eq18165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18165 eq18475
  have eq18864 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16323 eq17826
    | exact resolve eq17826 eq16323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16323 eq17826
  have eq18884 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18864 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18864
  have eq18894 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16632 eq18333
    | exact resolve eq18333 eq16632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16632 eq18333
  have eq18916 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18894 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18894
  have eq18923 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18916 X0
       grind)
    | (have r₁ := eq18916 X0
       have r₂ := eq16644
       grind)
    | exact resolve eq18916 eq16644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16644 eq18916
  have eq18968 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18494 eq18884
    | exact resolve eq18884 eq18494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18884
  have eq18988 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18968
  have eq19039 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18494 eq18923
    | exact resolve eq18923 eq18494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18494 eq18923
  have eq19059 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19039
  have eq19408 : y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18988 x
       grind)
    | exact superpose eq18988 eq19
    | (have j1 := eq18988 x
       grind)
    | exact resolve eq19 eq18988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18988
  have eq19414 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq19408
  have eq19775 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq19059 x
       grind)
    | exact superpose eq19059 eq19
    | (have j1 := eq19059 x
       grind)
    | exact resolve eq19 eq19059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19059
  have eq19781 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19775
  have eq19794 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19781 eq28
    | exact resolve eq28 eq19781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19781
  have eq19822 : y = (M.op x y) := by
    first
    | (have r₁ := eq19794
       have r₂ := eq19414
       grind)
    | exact resolve eq19794 eq19414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19414 eq19794
  have eq19980 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq19822 eq21
    | exact resolve eq21 eq19822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20027 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19822 eq229
    | exact resolve eq229 eq19822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq20050 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq19822 eq10248
    | exact resolve eq10248 eq19822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10248
  have eq20054 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq20050
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20050
    | exact resolve eq20050 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20050
  have eq20074 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq20027 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20027
    | (have j0 := eq20027 X0
       grind)
    | exact resolve eq20027 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20027
  have eq20120 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19980
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19980
    | exact resolve eq19980 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq19980
  have eq20122 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq20054
    | exact resolve eq20054 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq20054
  have eq20135 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq19822 eq20074
    | exact resolve eq20074 eq19822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20074
  have eq20162 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq19822 eq20122
    | exact resolve eq20122 eq19822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19822 eq20122
  have eq20183 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20120 eq27
    | exact resolve eq27 eq20120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20120
  have eq20717 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq20162 eq20183
    | exact resolve eq20183 eq20162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20183
  have eq20718 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20717
       have i₂ := eq20135 sF2
       grind)
    | exact superpose eq20135 eq20717
    | exact resolve eq20717 eq20135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20135 eq20717
  have eq20723 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq20718 eq28
    | exact resolve eq28 eq20718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20718
  have eq20756 : False := by grind
  exact eq20756

/-- `Equation4311`: `x ◇ (x ◇ y) = z ◇ (w ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4311 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4311 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4311.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq174 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X4 X5 : G, (M.op X4 (M.op X5 X4)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op x X2) X4 X5
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | (have i₁ := eq16 X0 (M.op X0 X1) X2 x
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | (have i₁ := eq16 X0 X1 X1 X1
       have i₂ := eq16 X1 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op y (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq180 x x
       have i₂ := eq181 x x
       grind)
    | exact superpose eq181 eq180
    | exact resolve eq180 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq187 : ∀ X2 X4 X5 : G, (M.op X4 (M.op X5 X4)) = (M.op X2 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq177 x x X2 X4 X5
       have i₂ := eq181 x x
       grind)
    | exact superpose eq181 eq177
    | exact resolve eq177 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq181
  have eq188 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq174 x x
       have i₂ := eq175 x x
       grind)
    | exact superpose eq175 eq174
    | exact resolve eq174 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq189 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X2
    first
    | (have i₁ := eq187 X2 x x
       have i₂ := eq175 x x
       grind)
    | exact superpose eq175 eq187
    | exact resolve eq187 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq190 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq186 eq16
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq193 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq189 eq190
    | exact resolve eq190 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq195 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq188 eq16
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq196 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq195 x x
       have i₂ := eq175 x x
       grind)
    | exact superpose eq175 eq195
    | exact resolve eq195 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq204 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y) (σ x)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op x X0) X2 X3
       have i₂ := eq175 X0 x
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq210 X0 x x
       have i₂ := eq175 x x
       grind)
    | exact superpose eq175 eq210
    | exact resolve eq210 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq210
  have eq271 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq189 eq13
    | (have j0 := eq13 X0 (M.op (σ y) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq271 X0
       grind)
    | (have r₁ := eq271 X0
       have r₂ := eq204
       grind)
    | exact resolve eq271 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq276 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq204 eq272
    | exact resolve eq272 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq353 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq211 (M.op sF2 sF4)
       have i₂ := eq276 (M.op sF2 sF4)
       grind)
    | exact superpose eq276 eq211
    | exact resolve eq211 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq549 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq576 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq492 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq492
    | exact resolve eq492 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq627 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | exact superpose eq276 eq549
    | exact resolve eq549 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq276
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1142 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1164 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq4626 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1142
       grind)
    | exact superpose eq1142 eq40
    | exact resolve eq40 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq4627 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4626
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4626
    | exact resolve eq4626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4626
  have eq4629 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq4627
    | exact resolve eq4627 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627
  have eq12669 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq276 (M.op sF2 sF4)
       have i₂ := eq1164 (M.op sF2 sF4)
       grind)
    | exact superpose eq1164 eq276
    | (have j1 := eq1164 X0
       grind)
    | exact resolve eq276 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq12774 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12669 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq12669 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq12669 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12669
  have eq12890 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq193 X0 X0
       have i₂ := eq12774 X0
       grind)
    | exact superpose eq12774 eq193
    | exact resolve eq193 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12898 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq627 X0
       have i₂ := eq12774 (σ X0)
       grind)
    | exact superpose eq12774 eq627
    | exact resolve eq627 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq12913 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12898 X0
       have i₂ := eq549 X0 (σ X0)
       grind)
    | exact superpose eq549 eq12898
    | exact resolve eq12898 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12898
  have eq12942 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12913 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12913
    | exact resolve eq12913 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12913
  have eq13765 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12890 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq12890
    | exact resolve eq12890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13766 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12890 (τ X0)
       have i₂ := eq576 X0 X0
       grind)
    | exact superpose eq576 eq12890
    | exact resolve eq12890 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15747 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq353 eq13765
    | exact resolve eq13765 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15847 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq15747
       have i₂ := eq276 (σ (M.op sF2 sF4))
       grind)
    | exact superpose eq276 eq15747
    | exact resolve eq15747 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq15747
  have eq19903 : (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq15847 eq549
    | exact resolve eq549 eq15847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq15847
  have eq19910 : (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq12942 eq19903
    | exact resolve eq19903 eq12942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12942 eq19903
  have eq19912 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq353 eq19910
    | exact resolve eq19910 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq19910
  have eq19926 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq19912 eq14
    | exact resolve eq14 eq19912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19912
  have eq31954 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4629 eq1149
    | exact resolve eq1149 eq4629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149 eq4629
  have eq31961 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq31954
       have r₂ := eq27
       grind)
    | exact resolve eq31954 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31954
  have eq31967 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31961
       have i₂ := eq12774 sF2
       grind)
    | exact superpose eq12774 eq31961
    | exact resolve eq31961 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31961
  have eq31971 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31967
       have i₂ := eq12774 sF3
       grind)
    | exact superpose eq12774 eq31967
    | exact resolve eq31967 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31967
  have eq31975 : y = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31971
       have i₂ := eq12774 x
       grind)
    | exact superpose eq12774 eq31971
    | exact resolve eq31971 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31971
  have eq31977 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq31975
       have i₂ := eq12774 y
       grind)
    | exact superpose eq12774 eq31975
    | exact resolve eq31975 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31975
  have eq32441 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq31977 eq152
    | exact resolve eq152 eq31977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq31977
  have eq32469 : y = (k y y) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq31 eq32441
    | exact resolve eq32441 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32441
  have eq32470 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ y = (k y y) := by grind
  clear eq32469
  have eq32490 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq32470 eq97
    | exact resolve eq97 eq32470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq32470
  have eq32515 : y = (k x x) ∨ y = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq32490
    | exact resolve eq32490 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq32490
  have eq32516 : y = (k y y) ∨ y = (k x x) := by grind
  clear eq32515
  have eq32530 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq32516
       grind)
    | exact superpose eq32516 eq40
    | exact resolve eq40 eq32516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32538 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq12890 y
       have i₂ := eq32516
       grind)
    | exact superpose eq32516 eq12890
    | exact resolve eq12890 eq32516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32539 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq13765 y
       have i₂ := eq32516
       grind)
    | exact superpose eq32516 eq13765
    | exact resolve eq13765 eq32516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32540 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq13766 y
       have i₂ := eq32516
       grind)
    | exact superpose eq32516 eq13766
    | exact resolve eq13766 eq32516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13766
  have eq32549 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq32540
       have i₂ := eq12774 (τ y)
       grind)
    | exact superpose eq12774 eq32540
    | exact resolve eq32540 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32540
  have eq32550 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq32539
       have i₂ := eq12774 (σ y)
       grind)
    | exact superpose eq12774 eq32539
    | exact resolve eq32539 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32539
  have eq32551 : (k y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq32538
       have i₂ := eq12774 y
       grind)
    | exact superpose eq12774 eq32538
    | exact resolve eq32538 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32538
  have eq32558 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq32530
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32530
    | exact resolve eq32530 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32530
  have eq32564 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (k y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq32549
       have i₂ := eq576 y y
       grind)
    | exact superpose eq576 eq32549
    | exact resolve eq32549 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq32549
  have eq32565 : (σ (k y y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq32550
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq32550
    | exact resolve eq32550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32550
  have eq32566 : y = (k x x) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32516 eq32551
    | exact resolve eq32551 eq32516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32551
  have eq32573 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ y) ∨ y = (k x x) := by
    first
    | exact superpose eq32516 eq32564
    | exact resolve eq32564 eq32516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32516 eq32564
  have eq32574 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq32565
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq32565
    | exact resolve eq32565 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq32565
  have eq32578 : y = (k x x) ∨ y = (τ y) := by
    first
    | exact superpose eq32566 eq32573
    | exact resolve eq32573 eq32566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32573
  have eq32579 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq32574
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32574
    | exact resolve eq32574 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32574
  have eq32583 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | exact superpose eq32558 eq32579
    | exact resolve eq32579 eq32558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32558 eq32579
  have eq32598 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq12890 x
       have i₂ := eq32578
       grind)
    | exact superpose eq32578 eq12890
    | exact resolve eq12890 eq32578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32599 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq13765 x
       have i₂ := eq32578
       grind)
    | exact superpose eq32578 eq13765
    | exact resolve eq13765 eq32578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32578
  have eq32604 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq32599
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32599
    | exact resolve eq32599 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32599
  have eq32605 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq32598
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32598
    | exact resolve eq32598 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32598
  have eq32616 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq32604
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32604
    | exact resolve eq32604 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32604
  have eq32623 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | exact superpose eq26 eq32616
    | exact resolve eq32616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32616
  have eq32626 : y = (τ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32605 eq32623
    | exact resolve eq32623 eq32605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32623
  have eq32631 : y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq32626
       grind)
    | exact superpose eq32626 eq14
    | exact resolve eq14 eq32626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32626
  have eq32677 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq32631
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32631
    | exact resolve eq32631 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32631
  have eq32692 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32677 eq27
    | exact resolve eq27 eq32677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32677
  have eq33221 : (M.op x y) = (σ (M.op x y)) ∨ y = (τ y) := by
    first
    | exact superpose eq32605 eq19926
    | exact resolve eq19926 eq32605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32605
  have eq33262 : y = (τ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq33221
    | exact resolve eq33221 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33221
  have eq33439 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq33262
       grind)
    | exact superpose eq33262 eq14
    | exact resolve eq14 eq33262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33262
  have eq33485 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq33439
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33439
    | exact resolve eq33439 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33439
  have eq33492 : y = (σ y) := by
    first
    | (have r₁ := eq33485
       have r₂ := eq32692
       grind)
    | exact resolve eq33485 eq32692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32692 eq33485
  have eq33508 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq33492
       grind)
    | exact superpose eq33492 eq18
    | exact resolve eq18 eq33492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33509 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq33492
       grind)
    | exact superpose eq33492 eq24
    | exact resolve eq24 eq33492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37215 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12890 x
       have i₂ := eq32566
       grind)
    | exact superpose eq32566 eq12890
    | exact resolve eq12890 eq32566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12890
  have eq37216 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13765 x
       have i₂ := eq32566
       grind)
    | exact superpose eq32566 eq13765
    | exact resolve eq13765 eq32566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13765 eq32566
  have eq37226 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37216
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37216
    | exact resolve eq37216 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37216
  have eq37227 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37215
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37215
    | exact resolve eq37215 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq37215
  have eq37243 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37226
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37226
    | exact resolve eq37226 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37226
  have eq37244 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37227
       have i₂ := eq33492
       grind)
    | exact superpose eq33492 eq37227
    | exact resolve eq37227 eq33492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37227
  have eq37260 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq37243
    | exact resolve eq37243 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37243
  have eq37272 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37260
       have i₂ := eq33492
       grind)
    | exact superpose eq33492 eq37260
    | exact resolve eq37260 eq33492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37260
  have eq37280 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37244 eq37272
    | exact resolve eq37272 eq37244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37244 eq37272
  have eq37296 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37280 eq211
    | exact resolve eq211 eq37280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37395 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37280 eq193
    | exact resolve eq193 eq37280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq37280
  have eq37398 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq37395
    | exact resolve eq37395 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37395
  have eq37681 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq37398
  have eq38054 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37296 eq33508
    | exact resolve eq33508 eq37296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37296
  have eq38059 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq38054
       have r₂ := eq37681
       grind)
    | exact resolve eq38054 eq37681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37681 eq38054
  have eq38082 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq38059 eq27
    | exact resolve eq27 eq38059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38088 : (M.op (σ x) (M.op x y)) = (M.op (σ y) (M.op x y)) := by
    first
    | exact superpose eq38059 eq204
    | exact resolve eq204 eq38059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq38089 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq38059 eq211
    | exact resolve eq211 eq38059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq38164 : (M.op (σ x) (M.op x y)) = (σ (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq38059 eq19926
    | exact resolve eq19926 eq38059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19926 eq38059
  have eq38301 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (M.op (σ x) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq38088 eq185
    | exact resolve eq185 eq38088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq38088
  have eq38305 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq38089 eq38301
    | exact resolve eq38301 eq38089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38089 eq38301
  have eq39368 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (σ x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq38305 X0 X0
       have i₂ := eq12774 X0
       grind)
    | exact superpose eq12774 eq38305
    | exact resolve eq38305 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12774 eq38305
  have eq40009 : (σ y) = (M.op x (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq32583 eq196
    | exact resolve eq196 eq32583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq32583
  have eq40210 : (M.op x y) = (σ y) ∨ y = (k x x) := by
    first
    | exact superpose eq33508 eq40009
    | exact resolve eq40009 eq33508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40009
  have eq40280 : (σ y) = (k x x) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq40210
       have i₂ := eq33492
       grind)
    | exact superpose eq33492 eq40210
    | exact resolve eq40210 eq33492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33492 eq40210
  have eq40415 : (M.op (σ x) (M.op x y)) = (M.op x (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq39368 x
       have i₂ := eq40280
       grind)
    | exact superpose eq40280 eq39368
    | exact resolve eq39368 eq40280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39368 eq40280
  have eq40419 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq33508 eq40415
    | exact resolve eq40415 eq33508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33508 eq40415
  have eq41258 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq40419 eq38164
    | exact resolve eq38164 eq40419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38164 eq40419
  have eq41291 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq41258
    | exact resolve eq41258 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41258
  have eq41302 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq41291
       have r₂ := eq38082
       grind)
    | exact resolve eq41291 eq38082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41291
  have eq41373 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41302 eq33509
    | exact resolve eq33509 eq41302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33509 eq41302
  have eq41644 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41373 eq20
    | exact resolve eq20 eq41373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq41373
  have eq41800 : False := by grind
  exact eq41800

/-- `Equation432`: `x = x ◇ (y ◇ (x ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pyx_Equation432 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law432 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law432.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq328 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq769 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X1) (σ X0)
       have i₂ := eq331 X0 X1
       grind)
    | exact superpose eq331 eq64
    | (have j1 := eq331 X1 X0
       grind)
    | exact resolve eq64 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X2 (M.op (σ X0) (σ (k X0 X1))))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 (σ X1)
       have i₂ := eq331 X1 X0
       grind)
    | exact superpose eq331 eq9
    | (have j1 := eq331 X1 X0
       grind)
    | exact resolve eq9 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq331
  have eq788 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq795 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq788 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq788
    | (have j0 := eq788 X0
       grind)
    | exact resolve eq788 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq4211 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) = (σ (k (τ X0) (τ (k X0 X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq795 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq795
    | (have j0 := eq795 (τ X0)
       grind)
    | exact resolve eq795 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4250 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) = (k (σ (τ X0)) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4211 X0
       have i₂ := eq20 (k X0 X0) (τ X0)
       grind)
    | exact superpose eq20 eq4211
    | (have j0 := eq4211 X0
       grind)
    | exact resolve eq4211 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4211
  have eq4271 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (σ (τ (k X0 X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4250 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4250
    | (have j0 := eq4250 X0
       grind)
    | exact resolve eq4250 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4250
  have eq4289 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4271 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq4271
    | (have j0 := eq4271 X0
       grind)
    | exact resolve eq4271 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4271
  have eq4303 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4289 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4289
    | (have j0 := eq4289 X0
       grind)
    | exact resolve eq4289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4289
  have eq7613 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq328 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq328
    | exact resolve eq328 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq7681 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7613 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7613
    | (have j0 := eq7613 X0 X1
       grind)
    | exact resolve eq7613 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7613
  have eq29541 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq769 (τ X1) (τ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq769
    | (have j0 := eq769 (τ X0) (τ X1)
       grind)
    | exact resolve eq769 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq29714 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29541 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29541
    | (have j0 := eq29541 X0 X1
       grind)
    | exact resolve eq29541 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29541
  have eq29757 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29714 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq29714
    | (have j0 := eq29714 X0 X1
       grind)
    | exact resolve eq29714 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29714
  have eq29796 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29757 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29757
    | (have j0 := eq29757 X0 X1
       grind)
    | exact resolve eq29757 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29757
  have eq29828 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29796 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29796
    | (have j0 := eq29796 X0 X1
       grind)
    | exact resolve eq29796 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29796
  have eq29845 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29828 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29828
    | (have j0 := eq29828 X0 X1
       grind)
    | exact resolve eq29828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29828
  have eq29858 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29845 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29845
    | (have j0 := eq29845 X0 X1
       grind)
    | exact resolve eq29845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29845
  have eq29959 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (k X0 X1)))) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 (k X0 X1)
       have i₂ := eq29858 X0 X1
       grind)
    | exact superpose eq29858 eq9
    | (have j1 := eq29858 X0 X1
       grind)
    | exact resolve eq9 eq29858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29858
  have eq47886 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (k X0 (k X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq770 X0 X0 X1
       have i₂ := eq795 X0
       grind)
    | exact superpose eq795 eq770
    | (have j0 := eq770 X0 X0 x
       have j1 := eq795 X0
       grind)
    | exact resolve eq770 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq795
  have eq47933 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (k X0 (k X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq47886 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47886
  have eq48287 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X1 (k X0 (σ (k (τ X0) (τ X0)))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq47933 (τ X0) X1
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq47933
    | (have j0 := eq47933 (τ X0) X1
       grind)
    | exact resolve eq47933 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq47933
  have eq48356 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X1 (k X0 (k (σ (τ X0)) X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48287 X0 X1
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq48287
    | (have j0 := eq48287 X0 X1
       grind)
    | exact resolve eq48287 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq48287
  have eq48386 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 (k X0 X0)))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48356 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48356
    | (have j0 := eq48356 X0 X1
       grind)
    | exact resolve eq48356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48356
  have eq48397 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 (k X0 X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48386 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48386
    | (have j0 := eq48386 X0 X1
       grind)
    | exact resolve eq48386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48386
  have eq48426 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (k X0 X0)))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48397 X0 X1
       have i₂ := eq4303 X0
       grind)
    | exact superpose eq4303 eq48397
    | (have j0 := eq48397 X0 X1
       have j1 := eq4303 X0
       grind)
    | exact resolve eq48397 eq4303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303
  have eq48468 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29959 X0 (k X0 X0) X0
       have i₂ := eq48397 X0 X0
       grind)
    | exact superpose eq48397 eq29959
    | (have j0 := eq29959 X0 X0 x
       have j1 := eq48397 X0 x
       grind)
    | exact resolve eq29959 eq48397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29959
  have eq48489 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48468 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48468
  have eq48491 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (k X0 X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48426 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48426
  have eq48992 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq48489
  have eq49140 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq48992 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48992
  have eq49462 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48397 X0 X1
       have i₂ := eq49140 X0
       grind)
    | exact superpose eq49140 eq48397
    | (have j0 := eq48397 X0 X1
       have j1 := eq49140 X0
       grind)
    | exact resolve eq48397 eq49140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48397 eq49140
  have eq49509 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49462
  have eq55396 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq48491 X0 X0
       have i₂ := eq49509 X0 X0
       grind)
    | exact superpose eq49509 eq48491
    | (have j0 := eq48491 X0 x
       have j1 := eq49509 X0 x
       grind)
    | exact resolve eq48491 eq49509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48491 eq49509
  have eq55420 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55396 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55396
  have eq55451 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq55420
  have eq55636 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55451
  have eq55964 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55636 (σ X0)
       grind)
    | exact superpose eq55636 eq15
    | exact resolve eq15 eq55636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56027 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55964 X0
       have i₂ := eq55636 X0
       grind)
    | exact superpose eq55636 eq55964
    | exact resolve eq55964 eq55636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55636 eq55964
  have eq57235 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq57383 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq56027 X0
       grind)
    | exact superpose eq56027 eq64
    | exact resolve eq64 eq56027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57547 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq57235 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq57235
    | exact resolve eq57235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57235
  have eq57730 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq57547
  have eq265173 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq327 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq327
    | exact resolve eq327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq265992 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq265173 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq265173
    | (have j0 := eq265173 X0 X1
       grind)
    | exact resolve eq265173 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq265173
  have eq266843 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq265992 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq265992
    | (have j0 := eq265992 (σ X1) (σ X0)
       grind)
    | exact resolve eq265992 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265992
  have eq267413 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq266843 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq266843
    | (have j0 := eq266843 X0 X1
       grind)
    | exact resolve eq266843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266843
  have eq267542 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq267413 X0 X1
       have i₂ := eq56027 X1
       grind)
    | exact superpose eq56027 eq267413
    | (have j0 := eq267413 X0 X1
       grind)
    | exact resolve eq267413 eq56027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267413
  have eq267632 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq267542 X0 X1
       have i₂ := eq56027 X0
       grind)
    | exact superpose eq56027 eq267542
    | (have j0 := eq267542 X0 X1
       grind)
    | exact resolve eq267542 eq56027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56027 eq267542
  have eq569997 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq267632 X0 X1
       grind)
    | exact superpose eq267632 eq11
    | (have j1 := eq267632 X0 X1
       grind)
    | exact resolve eq11 eq267632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267632
  have eq588154 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq569997 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq569997 X0 X1
       grind)
    | exact superpose eq569997 eq10
    | (have j1 := eq569997 X0 X1
       grind)
    | exact resolve eq10 eq569997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569997
  have eq588439 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq588154 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq588154
    | (have j0 := eq588154 X0 X1
       grind)
    | exact resolve eq588154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588154
  have eq591453 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq588439 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq588439 X0 X1
       grind)
    | exact superpose eq588439 eq10
    | (have j1 := eq588439 X1 X0
       grind)
    | exact resolve eq10 eq588439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588439
  have eq591736 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq591453 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq591453
    | (have j0 := eq591453 X0 X1
       grind)
    | exact resolve eq591453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591453
  have eq594199 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq591736 x y
       grind)
    | exact superpose eq591736 eq16
    | (have j1 := eq591736 x y
       grind)
    | exact resolve eq16 eq591736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591736
  have eq595936 : y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq7681 x y
       grind)
    | (have r₁ := eq594199
       have r₂ := eq7681 x y
       grind)
    | exact resolve eq594199 eq7681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7681 eq594199
  have eq599462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq57730 x
       have i₂ := eq595936
       grind)
    | exact superpose eq595936 eq57730
    | exact resolve eq57730 eq595936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57730 eq595936
  have eq599765 : x = (M.op y y) := by
    first
    | (have r₁ := eq599462
       have r₂ := eq16
       grind)
    | exact resolve eq599462 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599462
  have eq600156 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57383 y
       have i₂ := eq599765
       grind)
    | exact superpose eq599765 eq57383
    | exact resolve eq57383 eq599765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57383
  have eq600423 : x = (M.op x y) := by
    first
    | (have i₁ := eq64 y y
       have i₂ := eq599765
       grind)
    | exact superpose eq599765 eq64
    | exact resolve eq64 eq599765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq599765
  have eq602470 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq600156
       grind)
    | exact superpose eq600156 eq16
    | exact resolve eq16 eq600156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600156
  have eq602580 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq602470
       have i₂ := eq600423
       grind)
    | exact superpose eq600423 eq602470
    | exact resolve eq602470 eq600423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600423 eq602470
  have eq602581 : False := by grind
  exact eq602581

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact superpose eq32 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op X1 X1) X0
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq31
    | exact resolve eq31 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact superpose eq32 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 x x
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq59 X0 X0
       grind)
    | exact superpose eq59 eq32
    | (have j1 := eq59 X0 X0
       grind)
    | exact resolve eq32 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq59 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq103 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq102 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq139 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 X0) X1
       have i₂ := eq47 X0 (σ X1)
       grind)
    | exact superpose eq47 eq22
    | exact resolve eq22 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq148 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq44 X1 (σ X0)
       grind)
    | exact superpose eq44 eq28
    | exact resolve eq28 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq161 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148
    | exact resolve eq148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq171 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (τ (M.op X1 X1))
       have i₂ := eq161 (σ X0) X1
       grind)
    | exact superpose eq161 eq28
    | exact resolve eq28 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq161
  have eq175 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq171
    | exact resolve eq171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq614 : ∀ X0 : G, (σ (τ (τ (M.op X0 X0)))) ≠ (σ (τ (τ (M.op X0 X0)))) ∨ (σ (τ (τ (M.op X0 X0)))) = (M.op (σ (τ (τ (M.op X0 X0)))) (σ (τ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq103 (τ (τ (M.op X0 X0)))
       have i₂ := eq175 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq175 eq103
    | (have j0 := eq103 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq103 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq617 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq103 (M.op X0 X0)
       have i₂ := eq47 X0 (M.op X0 X0)
       grind)
    | exact superpose eq47 eq103
    | (have j0 := eq103 (M.op X0 X0)
       grind)
    | exact resolve eq103 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq103
  have eq626 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq629 : ∀ X0 : G, (σ (τ (τ (M.op X0 X0)))) = (M.op (σ (τ (τ (M.op X0 X0)))) (σ (τ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have j0 := eq614 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq644 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq629 X0
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq629
    | exact resolve eq629 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq717 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X0 (σ X0)
       have i₂ := eq108 X0 X1
       grind)
    | exact superpose eq108 eq43
    | (have j1 := eq108 X0 X2
       grind)
    | exact resolve eq43 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1337 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq91
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq91 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1338 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1337
  have eq2237 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ (M.op X0 X0)) X1
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq32
    | exact resolve eq32 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4022 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq717 X0 (σ (k X0 X0)) (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq4023 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq4022 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022
  have eq4075 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq4023 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4023
    | exact resolve eq4023 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4023
  have eq4082 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4075 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4075
    | exact resolve eq4075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4075
  have eq4133 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq31 (k X0 X0) X0
       have i₂ := eq4082 X0
       grind)
    | exact superpose eq4082 eq31
    | exact resolve eq31 eq4082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4082
  have eq11337 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (τ (M.op X0 X0))
       have i₂ := eq644 X0
       grind)
    | exact superpose eq644 eq43
    | exact resolve eq43 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq16946 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq626 y
       have i₂ := eq1338
       grind)
    | exact superpose eq1338 eq626
    | exact resolve eq626 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq16969 : x = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16946
  have eq134234 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq626 x
       have i₂ := eq16969
       grind)
    | exact superpose eq16969 eq626
    | exact resolve eq626 eq16969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq16969
  have eq134272 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq134234
  have eq232862 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq139 (σ y) x
       have i₂ := eq134272
       grind)
    | exact superpose eq134272 eq139
    | exact resolve eq139 eq134272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq134272
  have eq232946 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq232862 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq232862
    | exact resolve eq232862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232862
  have eq235622 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ y = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (σ x)
       have i₂ := eq232946 X0
       grind)
    | exact superpose eq232946 eq43
    | (have j1 := eq232946 X1
       grind)
    | exact resolve eq43 eq232946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq235666 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (τ (σ x)) X0) ∨ y = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11337 (σ x) X1
       have i₂ := eq232946 X0
       grind)
    | exact superpose eq232946 eq11337
    | (have j1 := eq232946 X1
       grind)
    | exact resolve eq11337 eq232946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11337 eq232946
  have eq235698 : ∀ X0 X1 : G, x = (M.op x X0) ∨ y = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq235666 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq235666
    | (have j0 := eq235666 X0 X1
       grind)
    | exact resolve eq235666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235666
  have eq253619 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq235622 (σ y) X0
       grind)
    | exact superpose eq235622 eq16
    | (have j1 := eq235622 X0 X0
       grind)
    | exact resolve eq16 eq235622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235622
  have eq267162 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ y = (k y X0) ∨ y = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq253619 X0
       have i₂ := eq235698 y X1
       grind)
    | exact superpose eq235698 eq253619
    | (have j0 := eq253619 X0
       have j1 := eq235698 X0 X0
       grind)
    | exact resolve eq253619 eq235698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235698 eq253619
  have eq267165 : ∀ X0 X1 : G, y = (k y X0) ∨ y = (k y X1) := by
    intro X0 X1
    first
    | (have j0 := eq267162 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267162
  have eq267813 : ∀ X0 : G, y ≠ y ∨ y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq267165 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267165
  have eq267814 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq267813 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267813
  have eq267947 : y = (M.op y y) := by
    first
    | (have i₁ := eq4133 y
       have i₂ := eq267814 y
       grind)
    | exact superpose eq267814 eq4133
    | exact resolve eq4133 eq267814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133 eq267814
  have eq268856 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 y X0
       have i₂ := eq267947
       grind)
    | exact superpose eq267947 eq32
    | exact resolve eq32 eq267947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq268882 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2237 y X0
       have i₂ := eq267947
       grind)
    | exact superpose eq267947 eq2237
    | exact resolve eq2237 eq267947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237 eq267947
  have eq272157 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq268882 (σ x)
       grind)
    | exact superpose eq268882 eq16
    | exact resolve eq16 eq268882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268882
  have eq272171 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq272157
       have i₂ := eq268856 x
       grind)
    | exact superpose eq268856 eq272157
    | exact resolve eq272157 eq268856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268856 eq272157
  have eq272172 : False := by grind
  exact eq272172

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_x_pyx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq32 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (M.op X1 X1) X0
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq32
    | exact resolve eq32 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq45 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq47 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq104 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq142 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op X1 X1)
       have i₂ := eq45 X1 (σ X0)
       grind)
    | exact superpose eq45 eq29
    | exact resolve eq29 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq142
    | exact resolve eq142 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq163 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (τ (M.op X1 X1))
       have i₂ := eq155 (σ X0) X1
       grind)
    | exact superpose eq155 eq29
    | exact resolve eq29 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq155
  have eq169 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq163 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq163
    | exact resolve eq163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq634 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq104 (M.op X0 X0)
       have i₂ := eq45 X0 (M.op X0 X0)
       grind)
    | exact superpose eq45 eq104
    | (have j0 := eq104 (M.op X0 X0)
       grind)
    | exact resolve eq104 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq642 : ∀ X0 : G, (σ (τ (τ (M.op X0 X0)))) ≠ (σ (τ (τ (M.op X0 X0)))) ∨ (σ (τ (τ (M.op X0 X0)))) = (M.op (σ (τ (τ (M.op X0 X0)))) (σ (τ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq104 (τ (τ (M.op X0 X0)))
       have i₂ := eq169 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq169 eq104
    | (have j0 := eq104 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq104 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq169
  have eq653 : ∀ X0 : G, (σ (τ (τ (M.op X0 X0)))) = (M.op (σ (τ (τ (M.op X0 X0)))) (σ (τ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have j0 := eq642 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq661 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq669 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq653 X0
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq653
    | exact resolve eq653 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq1394 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq92
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq1395 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1394
  have eq1722 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ (M.op X0 X0)) X1
       have i₂ := eq661 X0
       grind)
    | exact superpose eq661 eq33
    | exact resolve eq33 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq8562 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 (τ (M.op X0 X0))
       have i₂ := eq669 X0
       grind)
    | exact superpose eq669 eq44
    | exact resolve eq44 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq669
  have eq15892 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq661 y
       have i₂ := eq1395
       grind)
    | exact superpose eq1395 eq661
    | exact resolve eq661 eq1395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq15914 : y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq15892
  have eq128822 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq661 x
       have i₂ := eq15914
       grind)
    | exact superpose eq15914 eq661
    | exact resolve eq661 eq15914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq15914
  have eq128884 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq128822
  have eq128944 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq8562 (σ y) x
       have i₂ := eq128884
       grind)
    | exact superpose eq128884 eq8562
    | exact resolve eq8562 eq128884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128884
  have eq128984 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq128944 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq128944
    | exact resolve eq128944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128944
  have eq129158 : ∀ X0 X1 : G, (τ (σ y)) = (M.op (τ (σ y)) X0) ∨ y = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8562 (σ x) X1
       have i₂ := eq128984 X0
       grind)
    | exact superpose eq128984 eq8562
    | (have j1 := eq128984 X1
       grind)
    | exact resolve eq8562 eq128984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8562 eq128984
  have eq129203 : ∀ X0 X1 : G, y = (M.op y X0) ∨ y = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq129158 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq129158
    | (have j0 := eq129158 X0 X0
       grind)
    | exact resolve eq129158 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129158
  have eq129544 : ∀ X0 : G, y ≠ y ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq129203 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129203
  have eq129545 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq129544 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129544
  have eq129572 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1722 y X0
       have i₂ := eq129545 y
       grind)
    | exact superpose eq129545 eq1722
    | exact resolve eq1722 eq129545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722
  have eq129616 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq129545 (M.op X0 (M.op x x))
       grind)
    | exact superpose eq129545 eq9
    | exact resolve eq9 eq129545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129545
  have eq131804 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq129572 (σ x)
       grind)
    | exact superpose eq129572 eq16
    | exact resolve eq16 eq129572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129572
  have eq131813 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq131804
       have i₂ := eq129616 x
       grind)
    | exact superpose eq129616 eq131804
    | exact resolve eq131804 eq129616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129616 eq131804
  have eq131814 : False := by grind
  exact eq131814
