import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq37 X1
       grind)
    | exact superpose eq37 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq204 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq181
    | (have j0 := eq181 X0 X1
       grind)
    | exact resolve eq181 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq181
  have eq209 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq204 X1 X0
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq204 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq204 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq204
  have eq261 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq209
    | exact resolve eq209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq209 (σ X0) X1
       grind)
    | exact superpose eq209 eq15
    | (have j1 := eq209 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq275 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq261 (τ X1) X0
       grind)
    | exact superpose eq261 eq18
    | (have j1 := eq261 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq261
  have eq543 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq275
    | exact resolve eq275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq581 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq543 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq543
    | (have j0 := eq543 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq1282 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq266 x y
       grind)
    | exact superpose eq266 eq16
    | (have j1 := eq266 x y
       grind)
    | exact resolve eq16 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq1312 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1282
       have i₂ := eq581 y x
       grind)
    | exact superpose eq581 eq1282
    | (have j1 := eq581 (σ x) (σ y)
       grind)
    | (have r₁ := eq1282
       have r₂ := eq581 y x
       grind)
    | (have r₁ := eq1282
       have r₂ := eq581 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1282
       have r₂ := eq581 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1282 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq1282
  have eq1313 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1312
  have eq1388 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1313
       grind)
    | exact superpose eq1313 eq10
    | exact resolve eq10 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1434 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1388
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1388
    | exact resolve eq1388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1435 : x = y := by grind
  clear eq1434
  have eq1437 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1435
       grind)
    | exact superpose eq1435 eq16
    | exact resolve eq16 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq1438 : False := by grind
  exact eq1438

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_y_pyx_y_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op (M.op X0 X3) X3) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X0 X1) X2) X2) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X0 X1) X2)
       have i₂ := eq63 (M.op X0 X1) X2
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq96 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0) (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq63
    | exact resolve eq63 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op (σ (M.op X0 X0)) X1) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq9
    | exact resolve eq9 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq97 X0 (σ (M.op X0 X0))
       have i₂ := eq82 (M.op X0 X0)
       grind)
    | exact superpose eq82 eq97
    | exact resolve eq97 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq593 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X1 (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq98
    | (have j0 := eq98 X1 (σ X0)
       grind)
    | (have r₁ := eq98 X0 (σ X0)
       have r₂ := eq82 X0
       grind)
    | exact resolve eq98 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq598 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq593
    | (have j0 := eq593 X0 X1
       grind)
    | exact resolve eq593 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq614 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq639 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq614 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq614
    | (have j0 := eq614 X0 X1
       grind)
    | exact resolve eq614 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq653 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq639
    | (have j0 := eq639 X0 X1
       grind)
    | exact resolve eq639 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq656 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq653 X0 X1
       have j1 := eq598 X1 X0
       grind)
    | (have r₁ := eq653 X0 X1
       have r₂ := eq598 X0 X1
       grind)
    | (have r₁ := eq653 X1 X0
       have r₂ := eq598 X0 X1
       grind)
    | exact resolve eq653 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq653
  have eq769 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq656 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq656
    | exact resolve eq656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq656 x y
       grind)
    | exact superpose eq656 eq16
    | (have j1 := eq656 x y
       grind)
    | exact resolve eq16 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq656 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq838 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq769 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq769
    | (have j0 := eq769 X0 X1
       grind)
    | exact resolve eq769 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq769
  have eq902 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq838 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq838
    | exact resolve eq838 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq964 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq902 (τ X1) X0
       grind)
    | exact superpose eq902 eq17
    | (have j1 := eq902 (τ X1) X0
       grind)
    | exact resolve eq17 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq902
  have eq1146 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq964 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq964
    | exact resolve eq964 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1146 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1146
    | (have j0 := eq1146 X0 X1
       grind)
    | exact resolve eq1146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1570 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq778
       have i₂ := eq1217 y x
       grind)
    | exact superpose eq1217 eq778
    | (have j1 := eq1217 (σ y) (σ x)
       grind)
    | (have r₁ := eq778
       have r₂ := eq1217 y x
       grind)
    | exact resolve eq778 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq1571 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1570
  have eq1575 : x ≠ x ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1571
       grind)
    | exact superpose eq1571 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1571
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1571
       grind)
    | exact resolve eq13 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1578 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63 x y
       have i₂ := eq1571
       grind)
    | exact superpose eq1571 eq63
    | exact resolve eq63 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571
  have eq1580 : x = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1575
  have eq1587 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63 (σ x) (σ y)
       have i₂ := eq1578
       grind)
    | exact superpose eq1578 eq63
    | exact resolve eq63 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1590 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1587
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq1587
    | exact resolve eq1587 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587
  have eq1602 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq96 x
       have i₂ := eq1590
       grind)
    | exact superpose eq1590 eq96
    | exact resolve eq96 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1590
  have eq1623 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1602
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq1602
    | exact resolve eq1602 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1624 : (σ x) = (σ (M.op x x)) := by grind
  clear eq1623
  have eq1633 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1624
       grind)
    | exact superpose eq1624 eq10
    | exact resolve eq10 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1679 : x = (M.op x x) := by
    first
    | (have i₁ := eq1633
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1633
    | exact resolve eq1633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq1855 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X4) X4) (M.op (M.op X0 X3) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X0 X3) X3) (M.op (M.op (M.op X0 X1) X2) X2) X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq21754 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1855 X0 X1 (M.op X0 X1) X2 (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq1855
    | exact resolve eq1855 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq22247 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21754 X0 X1 (M.op X0 X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq21754
    | exact resolve eq21754 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq21754
  have eq82198 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq810 x y
       have i₂ := eq1580
       grind)
    | exact superpose eq1580 eq810
    | (have j0 := eq810 x y
       grind)
    | exact resolve eq810 eq1580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq1580
  have eq82252 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq82198
  have eq82253 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq82252
  have eq82279 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82253
       have i₂ := eq1679
       grind)
    | exact superpose eq1679 eq82253
    | exact resolve eq82253 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82253
  have eq82301 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82279
       grind)
    | exact superpose eq82279 eq16
    | exact resolve eq16 eq82279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82324 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq82279
       grind)
    | exact superpose eq82279 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq82279
       grind)
    | exact resolve eq13 eq82279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82279
  have eq82357 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq82324
  have eq82367 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82357
       have i₂ := eq82 y
       grind)
    | exact superpose eq82 eq82357
    | exact resolve eq82357 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82357
  have eq82383 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82367
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq82367
    | exact resolve eq82367 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82367
  have eq82386 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82383
       have i₂ := eq1624
       grind)
    | exact superpose eq1624 eq82383
    | exact resolve eq82383 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82383
  have eq82387 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82386
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq82386
    | exact resolve eq82386 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82386
  have eq82400 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1217 y x
       have i₂ := eq82387
       grind)
    | exact superpose eq82387 eq1217
    | (have j0 := eq1217 y x
       grind)
    | exact resolve eq1217 eq82387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217 eq82387
  have eq82508 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq82400
       have r₂ := eq82301
       grind)
    | exact resolve eq82400 eq82301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82400
  have eq82656 : (M.op y y) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq82508
       grind)
    | exact superpose eq82508 eq10
    | exact resolve eq10 eq82508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82508
  have eq82760 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82656
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq82656
    | exact resolve eq82656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82656
  have eq82761 : x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq82760
  have eq82773 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82301
       have i₂ := eq82761
       grind)
    | exact superpose eq82761 eq82301
    | exact resolve eq82301 eq82761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82301 eq82761
  have eq82872 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by grind
  clear eq82773
  have eq82873 : x = (M.op y y) := by grind
  clear eq82872
  have eq82912 : (σ y) = (M.op (M.op (σ (M.op x x)) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq137 y
       have i₂ := eq82873
       grind)
    | exact superpose eq82873 eq137
    | exact resolve eq137 eq82873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq83033 : ∀ X0 : G, (M.op x x) = (M.op (M.op y X0) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq22247 y y x
       have i₂ := eq82873
       grind)
    | exact superpose eq82873 eq22247
    | exact resolve eq22247 eq82873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22247 eq82873
  have eq83063 : ∀ X0 : G, x = (M.op (M.op y X0) x) := by
    intro X0
    first
    | (have i₁ := eq83033 X0
       have i₂ := eq1679
       grind)
    | exact superpose eq1679 eq83033
    | exact resolve eq83033 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83033
  have eq83077 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq82912
       have i₂ := eq1624
       grind)
    | exact superpose eq1624 eq82912
    | exact resolve eq82912 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82912
  have eq83087 : (σ y) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq83077
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq83077
    | exact resolve eq83077 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq83077
  have eq83089 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83087
       have i₂ := eq1624
       grind)
    | exact superpose eq1624 eq83087
    | exact resolve eq83087 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624 eq83087
  have eq83353 : y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq67 y x x
       have i₂ := eq83063 x
       grind)
    | exact superpose eq83063 eq67
    | exact resolve eq67 eq83063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq83063
  have eq83423 : y = (M.op x y) := by
    first
    | (have i₁ := eq83353
       have i₂ := eq1679
       grind)
    | exact superpose eq1679 eq83353
    | exact resolve eq83353 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679 eq83353
  have eq84228 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83089
       grind)
    | exact superpose eq83089 eq16
    | exact resolve eq16 eq83089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83089
  have eq84380 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq84228
       have i₂ := eq83423
       grind)
    | exact superpose eq83423 eq84228
    | exact resolve eq84228 eq83423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83423 eq84228
  have eq84381 : False := by grind
  exact eq84381

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyy_x_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq15
    | exact resolve eq15 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq69 (τ X0)
       grind)
    | exact superpose eq69 eq32
    | exact resolve eq32 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq81 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq74
    | exact resolve eq74 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq72
  have eq97 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq64
    | exact resolve eq64 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X1 (σ X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq99
    | (have j0 := eq99 X1 (σ X0)
       grind)
    | (have r₁ := eq99 X0 (σ X0)
       have r₂ := eq83 X0
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq568 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq563
    | (have j0 := eq563 X0 X1
       grind)
    | exact resolve eq563 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq591 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq616 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq591
    | (have j0 := eq591 X0 X1
       grind)
    | exact resolve eq591 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq632 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq616
    | (have j0 := eq616 X0 X1
       grind)
    | exact resolve eq616 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq644 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq632
    | (have j0 := eq632 X0 X1
       grind)
    | exact resolve eq632 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq632
  have eq647 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       have j1 := eq568 X1 X0
       grind)
    | (have r₁ := eq644 X0 X1
       have r₂ := eq568 X0 X1
       grind)
    | (have r₁ := eq644 X1 X0
       have r₂ := eq568 X0 X1
       grind)
    | (have r₁ := eq644 X1 (M.op X0 X0)
       have r₂ := eq568 X0 X1
       grind)
    | exact resolve eq644 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq644
  have eq652 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq647
    | exact resolve eq647 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq647 x y
       grind)
    | exact superpose eq647 eq16
    | (have j1 := eq647 x y
       grind)
    | exact resolve eq16 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq698 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq652
    | (have j0 := eq652 X0 X1
       grind)
    | exact resolve eq652 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq652
  have eq712 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq698
    | (have j0 := eq698 X1 (τ X0)
       grind)
    | exact resolve eq698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq743 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq712
    | (have j0 := eq712 X0 X1
       grind)
    | exact resolve eq712 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq712
  have eq744 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq743 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq743
    | (have j0 := eq743 X0 X1
       grind)
    | exact resolve eq743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq822 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq657
       have i₂ := eq744 x y
       grind)
    | exact superpose eq744 eq657
    | (have j1 := eq744 x y
       grind)
    | exact resolve eq657 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq744
  have eq825 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq822
  have eq829 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq825
       grind)
    | exact superpose eq825 eq64
    | exact resolve eq64 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq97 x
       have i₂ := eq825
       grind)
    | exact superpose eq825 eq97
    | exact resolve eq97 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq849 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq834
       grind)
    | exact superpose eq834 eq16
    | exact resolve eq16 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq860 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq849
       have i₂ := eq829
       grind)
    | exact superpose eq829 eq849
    | exact resolve eq849 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq849
  have eq861 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq860
  have eq862 : (σ y) = (σ (M.op x x)) := by grind
  clear eq861
  have eq867 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97 x
       have i₂ := eq862
       grind)
    | exact superpose eq862 eq97
    | exact resolve eq97 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq868 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq862
       grind)
    | exact superpose eq862 eq10
    | exact resolve eq10 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq910 : y = (M.op x x) := by
    first
    | (have i₁ := eq868
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq868
    | exact resolve eq868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq914 : y = (M.op x y) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq910
       grind)
    | exact superpose eq910 eq64
    | exact resolve eq64 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq910
  have eq938 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq16
    | exact resolve eq16 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq947 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq938
       have i₂ := eq914
       grind)
    | exact superpose eq914 eq938
    | exact resolve eq938 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq938
  have eq948 : False := by grind
  exact eq948

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_pyx_y_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq304 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq306 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq299 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq307 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq305 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq305 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq305 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq318 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq307 (σ X0)
       grind)
    | exact superpose eq307 eq15
    | exact resolve eq15 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq307 (τ X0)
       grind)
    | exact superpose eq307 eq31
    | exact resolve eq31 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq331 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq324 X0
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq324
    | exact resolve eq324 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq337 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq318 X0
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq318
    | exact resolve eq318 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq318
  have eq402 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (τ X0) (τ X0)
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq63
    | exact resolve eq63 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq306 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq600 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq599 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq623 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq600 (τ X1) X0
       grind)
    | exact superpose eq600 eq17
    | (have j1 := eq600 (τ X1) X0
       grind)
    | exact resolve eq17 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq600
  have eq1007 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (τ X1) X0
       have i₂ := eq623 X0 X1
       grind)
    | exact superpose eq623 eq63
    | (have j1 := eq623 (τ X0) X0
       grind)
    | exact resolve eq63 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq623
  have eq1015 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1007 X0 X1
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq1007
    | (have j0 := eq1007 X0 X1
       grind)
    | exact resolve eq1007 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1138 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1015 (σ X0) X1
       have i₂ := eq337 X0
       grind)
    | exact superpose eq337 eq1015
    | (have j0 := eq1015 (σ X0) X1
       grind)
    | exact resolve eq1015 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1173 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1138 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1138
    | (have j0 := eq1138 X0 X1
       grind)
    | exact resolve eq1138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1175 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1173 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1173
    | (have j0 := eq1173 X0 X1
       grind)
    | exact resolve eq1173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1176 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1175 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1175
    | (have j0 := eq1175 X0 X1
       grind)
    | exact resolve eq1175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1177 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1176 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1176
    | (have j0 := eq1176 X0 X1
       grind)
    | exact resolve eq1176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1186 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0
       have i₂ := eq1177 X0 X1
       grind)
    | exact superpose eq1177 eq402
    | (have j1 := eq1177 (τ X0) X1
       grind)
    | exact resolve eq402 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq1177
  have eq1217 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1186 X0 X1
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq1186
    | (have j0 := eq1186 X0 X1
       grind)
    | exact resolve eq1186 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1306 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ (k (σ X0) X1)) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 (σ X0) X1
       have i₂ := eq337 X0
       grind)
    | exact superpose eq337 eq1217
    | (have j0 := eq1217 (σ X0) X1
       grind)
    | exact resolve eq1217 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq1217
  have eq1338 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k (σ X0) X1)) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1306 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1306
    | (have j0 := eq1306 X0 X1
       grind)
    | exact resolve eq1306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1340 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (M.op X1 (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1338 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1338
    | (have j0 := eq1338 X0 X1
       grind)
    | exact resolve eq1338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq1412 : ∀ X0 X1 : G, (k (σ X1) X0) = (τ (σ (M.op X0 (σ X1)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (σ X1) X0)
       have i₂ := eq1340 X1 X0
       grind)
    | exact superpose eq1340 eq10
    | (have j1 := eq1340 X1 X1
       grind)
    | exact resolve eq10 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1454 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1412 X0 X1
       have i₂ := eq10 (M.op X0 (σ X1))
       grind)
    | exact superpose eq10 eq1412
    | (have j0 := eq1412 X0 X1
       grind)
    | exact resolve eq1412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1456 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1454 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1454
    | (have j0 := eq1454 X0 (τ X0)
       grind)
    | exact resolve eq1454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1489 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1456 X0 X1
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq1456
    | (have j0 := eq1456 X0 X1
       grind)
    | exact resolve eq1456 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq1456
  have eq1500 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq1489 X0 X1
       grind)
    | exact superpose eq1489 eq11
    | (have j1 := eq1489 X0 X1
       grind)
    | exact resolve eq11 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1518 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1500 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1500
    | (have j0 := eq1500 X0 X1
       grind)
    | exact resolve eq1500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq1526 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1518 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1518 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1518 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1547 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1526 (σ X1) (σ X0)
       grind)
    | exact superpose eq1526 eq15
    | exact resolve eq15 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1574 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1547 X0 X1
       have i₂ := eq1526 X1 X0
       grind)
    | exact superpose eq1526 eq1547
    | exact resolve eq1547 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526 eq1547
  have eq2094 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1574 x y
       grind)
    | exact superpose eq1574 eq16
    | (have r₁ := eq16
       have r₂ := eq1574 x y
       grind)
    | exact resolve eq16 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq2127 : False := by grind
  exact eq2127

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_pyy_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = (M.op X2 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq44 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = (M.op X2 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq43 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq309 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq310 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq315 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq310 X0 X1
       have j1 := eq110 X0 X1
       grind)
    | (have r₁ := eq310 X0 X1
       have r₂ := eq110 X0 X1
       grind)
    | (have r₁ := eq310 X0 X0
       have r₂ := eq110 X0 X0
       grind)
    | exact resolve eq310 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq310
  have eq328 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq315 (σ X1) (σ X0)
       grind)
    | exact superpose eq315 eq15
    | exact resolve eq15 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X0 X1
       have i₂ := eq315 X1 X0
       grind)
    | exact superpose eq315 eq328
    | exact resolve eq328 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq328
  have eq335 : False := by grind
  exact eq335

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_pyy_pxy_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq68
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x x) = (k y x) := by
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
  have eq93 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq911 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq77
  have eq958 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq911 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq911
    | (have j0 := eq911 y X0
       grind)
    | exact resolve eq911 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq911
  have eq9415 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq958 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq958
    | (have j0 := eq958 x
       grind)
    | exact resolve eq958 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq958
  have eq9451 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9415
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq9415
    | exact resolve eq9415 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9415
  have eq9472 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq9451
    | exact resolve eq9451 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9451
  have eq9480 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq9472
    | exact resolve eq9472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9472
  have eq9486 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9480
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq9480
    | exact resolve eq9480 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9480
  have eq9492 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq9486
    | exact resolve eq9486 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9486
  have eq19955 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq19955
    | exact resolve eq19955 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19955
  have eq19967 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19956
       have r₂ := eq27
       grind)
    | exact resolve eq19956 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19956
  have eq19971 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq19967
    | exact resolve eq19967 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19967
  have eq19973 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq19971
    | exact resolve eq19971 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19971
  have eq19975 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19973 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19973
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19973
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19973
       grind)
    | exact resolve eq13 eq19973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19973
  have eq20020 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19975
       have r₂ := eq26
       grind)
    | exact resolve eq19975 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19975
  have eq20333 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20020 eq118
    | exact resolve eq118 eq20020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20020
  have eq20341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq20333
  have eq20343 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq20341
       have r₂ := eq27
       grind)
    | exact resolve eq20341 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20341
  have eq20560 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20343 eq93
    | (have r₁ := eq93
       have r₂ := eq20343
       grind)
    | exact resolve eq93 eq20343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20343
  have eq20652 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq20560
  have eq21935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20652 eq118
    | exact resolve eq118 eq20652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20652
  have eq21943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq21935
  have eq21945 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq21943
       have r₂ := eq27
       grind)
    | exact resolve eq21943 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21943
  have eq21947 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21945 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq21945
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21945
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21945
       grind)
    | exact resolve eq13 eq21945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21945
  have eq21998 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq21947
       have r₂ := eq26
       grind)
    | exact resolve eq21947 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21947
  have eq22755 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21998 eq118
    | exact resolve eq118 eq21998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq21998
  have eq22763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq22755
  have eq22765 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq22763
       have r₂ := eq27
       grind)
    | exact resolve eq22763 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22763
  have eq22767 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq22765
       grind)
    | exact superpose eq22765 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq22765
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22765
       grind)
    | exact resolve eq13 eq22765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22765
  have eq22818 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq22767
       have r₂ := eq18
       grind)
    | exact resolve eq22767 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22767
  have eq22871 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq22818
       grind)
    | exact superpose eq22818 eq100
    | exact resolve eq100 eq22818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22818
  have eq22889 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq22871
    | exact resolve eq22871 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22871
  have eq22930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq22889 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq22889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq22930
    | exact resolve eq22930 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22930
  have eq22948 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq22937
       have r₂ := eq27
       grind)
    | exact resolve eq22937 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22937
  have eq22952 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq22948
    | exact resolve eq22948 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22948
  have eq22954 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq22952
    | exact resolve eq22952 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22952
  have eq25225 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq22954 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq22954
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22954
       grind)
    | exact resolve eq13 eq22954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22954
  have eq25282 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq25225
       have r₂ := eq26
       grind)
    | exact resolve eq25225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25225
  have eq25357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq25282 eq22889
    | exact resolve eq22889 eq25282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25282
  have eq25363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq25357
  have eq25371 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq25363
       have r₂ := eq27
       grind)
    | exact resolve eq25363 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25363
  have eq25374 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq25371 eq93
    | (have r₁ := eq93
       have r₂ := eq25371
       grind)
    | exact resolve eq93 eq25371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq25371
  have eq25474 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq25374
  have eq26088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq25474 eq22889
    | exact resolve eq22889 eq25474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25474
  have eq26094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq26088
  have eq26102 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq26094
       have r₂ := eq27
       grind)
    | exact resolve eq26094 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26094
  have eq26104 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26102 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq26102
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq26102
       grind)
    | exact resolve eq13 eq26102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26102
  have eq26161 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq26104
       have r₂ := eq26
       grind)
    | exact resolve eq26104 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26104
  have eq26236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26161 eq22889
    | exact resolve eq22889 eq26161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22889 eq26161
  have eq26242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq26236
  have eq26250 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq26242
       have r₂ := eq27
       grind)
    | exact resolve eq26242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26242
  have eq26254 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq26250
       grind)
    | exact superpose eq26250 eq72
    | exact resolve eq72 eq26250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq26255 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq26250
       grind)
    | exact superpose eq26250 eq92
    | (have r₁ := eq92
       have r₂ := eq26250
       grind)
    | exact resolve eq92 eq26250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq26250
  have eq26355 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq26255
  have eq26368 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq26254
    | exact resolve eq26254 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26254
  have eq27974 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26368 eq9492
    | exact resolve eq9492 eq26368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9492 eq26368
  have eq27975 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq27974
       have r₂ := eq27
       grind)
    | exact resolve eq27974 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27974
  have eq28106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq26355
       grind)
    | exact superpose eq26355 eq100
    | exact resolve eq100 eq26355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26355
  have eq28126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq28106
    | exact resolve eq28106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28106
  have eq28373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28126 eq27975
    | exact resolve eq27975 eq28126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28382 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq28373
       have r₂ := eq27
       grind)
    | exact resolve eq28373 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28373
  have eq28558 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28382 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq28382
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28382
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq28382
       grind)
    | exact resolve eq13 eq28382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28382
  have eq28617 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq28558
       have r₂ := eq26
       grind)
    | exact resolve eq28558 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28558
  have eq29184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28617 eq28126
    | exact resolve eq28126 eq28617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28126 eq28617
  have eq29186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq29184
  have eq29190 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq29186
       have r₂ := eq27
       grind)
    | exact resolve eq29186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29186
  have eq29192 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq29190
       grind)
    | exact superpose eq29190 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq29190
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq29190
       grind)
    | exact resolve eq13 eq29190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29190
  have eq29251 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq29192
       have r₂ := eq18
       grind)
    | exact resolve eq29192 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq29192
  have eq29399 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq29251
       grind)
    | exact superpose eq29251 eq100
    | exact resolve eq100 eq29251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq29251
  have eq29421 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq29399
    | exact resolve eq29399 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq29399
  have eq29478 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq29421 eq27975
    | exact resolve eq27975 eq29421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27975
  have eq29482 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq29478
       have r₂ := eq27
       grind)
    | exact resolve eq29478 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29478
  have eq29536 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq29482 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq29482
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq29482
       grind)
    | exact resolve eq13 eq29482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29482
  have eq29595 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq29536
       have r₂ := eq26
       grind)
    | exact resolve eq29536 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq29536
  have eq29597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29421 eq29595
    | exact resolve eq29595 eq29421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29421 eq29595
  have eq29599 : False := by grind
  exact eq29599

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_pyx_pyx_pxy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31 (σ X0)
       grind)
    | exact superpose eq31 eq15
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq33
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33
  have eq71 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq400 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq80 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq80 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq80 X0 X0
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq80 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq13
    | (have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq425 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq401 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq434 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       have j1 := eq71 X0 (σ X1)
       grind)
    | (have r₁ := eq425 X0 X1
       have r₂ := eq71 X0 (σ X1)
       grind)
    | exact resolve eq425 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq435 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq400 X0 X1
       have j1 := eq71 X0 (σ X1)
       grind)
    | (have r₁ := eq400 X0 X1
       have r₂ := eq71 X0 (σ X1)
       grind)
    | exact resolve eq400 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq400
  have eq446 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq434
    | (have j0 := eq434 X0 X1
       grind)
    | exact resolve eq434 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq447 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq446 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq448 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq435 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq435
    | (have j0 := eq435 X0 X1
       grind)
    | exact resolve eq435 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq456 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq447
    | (have j0 := eq447 X0 X1
       grind)
    | exact resolve eq447 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq447
  have eq457 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq448
    | (have j0 := eq448 X0 X1
       grind)
    | exact resolve eq448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq458 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq461 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq458 X0 X1
       have j1 := eq456 X0 X1
       grind)
    | (have r₁ := eq458 X0 X1
       have r₂ := eq456 X0 X1
       grind)
    | exact resolve eq458 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq458
  have eq463 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq461 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq461
    | exact resolve eq461 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq461 x y
       grind)
    | exact superpose eq461 eq16
    | exact resolve eq16 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq571 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq463 X0 (τ X1)
       grind)
    | exact superpose eq463 eq17
    | exact resolve eq17 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq463
  have eq593 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq571 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq571
    | exact resolve eq571 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq604 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq593
    | exact resolve eq593 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq621 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq475
       have i₂ := eq604 x y
       grind)
    | exact superpose eq604 eq475
    | exact resolve eq475 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq604
  have eq622 : False := by grind
  exact eq622

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyy_pyx_pxy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op (M.op X0 X3) X3) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X0 X1) X2) X2) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X1 X1) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X2) X0) X0 X1
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X0 X1) X2)
       have i₂ := eq46 (M.op X0 X1) X2
       grind)
    | exact superpose eq46 eq9
    | exact resolve eq9 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (k (M.op (M.op (M.op X1 X2) X0) X0) X1) = (M.op X1 (M.op (M.op (M.op X1 X2) X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X0) X1
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X1 X2) X0) X0) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X0 X1) X2) X2) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq54 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X1 X2) X0) X0) X1) = (M.op X1 (M.op (M.op (M.op X1 X2) X0) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq51 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq57 : ∀ X0 X1 : G, (k (τ X0) (τ (M.op X0 X1))) = (τ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X0 X1) X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq23
    | exact resolve eq23 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k (σ X0) (σ (M.op X0 X1))) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op X0 X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq15
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X0) (M.op (M.op (M.op X1 X2) X0) X0)) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq45 X0 (M.op (M.op (M.op X0 X1) X2) X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op (M.op (M.op (M.op X2 X0) X1) X3) X3) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X2 X0) X1) X3
       have i₂ := eq45 X1 X2 X0
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq104 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq104 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq23
    | exact resolve eq23 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq15
    | exact resolve eq15 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq105 (σ X0)
       grind)
    | exact superpose eq105 eq107
    | exact resolve eq107 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq105 (τ X0)
       grind)
    | exact superpose eq105 eq106
    | exact resolve eq106 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq106
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq10
    | exact resolve eq10 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq153 X0 X1
       grind)
    | exact superpose eq153 eq15
    | (have j1 := eq153 X0 X1
       grind)
    | exact resolve eq15 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq155 y x
       grind)
    | exact superpose eq155 eq16
    | (have j1 := eq155 y x
       grind)
    | exact resolve eq16 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq179 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq161
       have i₂ := eq153 (σ y) (σ x)
       grind)
    | exact superpose eq153 eq161
    | (have j1 := eq153 y x
       grind)
    | (have r₁ := eq161
       have r₂ := eq153 (σ y) (σ x)
       grind)
    | exact resolve eq161 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq161
  have eq180 : (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq179
  have eq192 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq108 y
       have i₂ := eq180
       grind)
    | exact superpose eq180 eq108
    | exact resolve eq108 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq196 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq192
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq192
    | exact resolve eq192 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq197 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq196
  have eq202 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ y) X0
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq9
    | exact resolve eq9 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq46 (σ y) (σ y)
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq46
    | exact resolve eq46 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq109 (σ y)
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq109
    | exact resolve eq109 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq214 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (σ y)
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq197
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq197
       grind)
    | exact resolve eq13 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (M.op y y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq212
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq212
    | exact resolve eq212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq222 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq218
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq218
    | exact resolve eq218 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq224 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op x x) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq222
       grind)
    | exact superpose eq222 eq9
    | exact resolve eq9 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq222
       grind)
    | exact superpose eq222 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq222
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq222
       grind)
    | exact resolve eq13 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op x x) (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1 y X0
       have i₂ := eq222
       grind)
    | exact superpose eq222 eq45
    | exact resolve eq45 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op x X0) X1) (M.op (M.op x X0) X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq224 (M.op (M.op x X0) X1)
       have i₂ := eq45 X1 x X0
       grind)
    | exact superpose eq45 eq224
    | exact resolve eq224 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X2 X0) X1) X1)) (τ X2)) = (τ (M.op X2 (M.op (M.op (M.op X2 X0) X1) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (M.op (M.op (M.op X2 X0) X1) X1)
       have i₂ := eq54 X1 X2 X0
       grind)
    | exact superpose eq54 eq23
    | exact resolve eq23 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54
  have eq384 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op (σ x) X0) X1) (M.op (M.op (σ x) X0) X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq202 (M.op (M.op (σ x) X0) X1)
       have i₂ := eq45 X1 (σ x) X0
       grind)
    | exact superpose eq45 eq202
    | exact resolve eq202 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq202
  have eq568 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X3) X2) X2) = (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X3) X2) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44 (M.op (M.op X0 X1) X0) X3 X2 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X4) X4) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X0) X3) X3) (M.op (M.op X1 X4) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq44 (M.op (M.op (M.op X0 X1) X2) X2) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq864 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq236 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq870 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq864
       grind)
    | exact superpose eq864 eq15
    | exact resolve eq15 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq878 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq870
       grind)
    | exact superpose eq870 eq16
    | exact resolve eq16 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq2635 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq574 (M.op X0 X1) X0 X1 (M.op X0 X1) X2
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq574
    | exact resolve eq574 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2683 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) X3) X4) X4) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq574 X0 (M.op (M.op X0 X1) X0) X2 X3 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq574
    | exact resolve eq574 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq2809 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2635 X0 X1 (M.op X0 X1)
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq2635
    | exact resolve eq2635 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2851 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2635 (M.op (M.op X0 X1) X0) X1 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq2635
    | exact resolve eq2635 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2930 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) (M.op (M.op X1 X0) X0)) = (M.op (M.op (M.op X1 X0) X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) (M.op (M.op X0 X2) X2)
       have i₂ := eq2635 X0 X1 X2
       grind)
    | exact superpose eq2635 eq53
    | exact resolve eq53 eq2635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4430 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op (M.op X0 X2) (M.op X0 X2)) X3) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2683 (M.op X0 X1) (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X0 X2) X3
       have i₂ := eq69 (M.op X0 X1) X0 X1 X2
       grind)
    | exact superpose eq69 eq2683
    | exact resolve eq2683 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4472 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X3) X0) X2) X1) X1) X0) X4) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2635 (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) X3) X0) X1 X0
       have i₂ := eq2683 X0 X1 X2 X3 X0
       grind)
    | exact superpose eq2683 eq2635
    | exact resolve eq2635 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635 eq2683
  have eq5664 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X2) X0) X4) = (M.op (M.op (M.op X3 X1) (M.op X3 X1)) (M.op (M.op (M.op X3 X2) X0) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4430 (M.op (M.op X3 X2) X0) X4 X0 (M.op X3 X1)
       have i₂ := eq69 X0 X3 X2 X1
       grind)
    | exact superpose eq69 eq4430
    | exact resolve eq4430 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq4430
  have eq5931 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X4) X4) X0) X3) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4472 X0 X4 (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X1 X3
       have i₂ := eq2809 (M.op X0 X1) X2 X0
       grind)
    | exact superpose eq2809 eq4472
    | exact resolve eq4472 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2809 eq4472
  have eq7026 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X3) X3) = (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X1) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq568 (M.op (M.op X2 X0) X1) (M.op (M.op X2 X0) X1) X2 (M.op X2 X2)
       have i₂ := eq76 X0 X1 X2 (M.op (M.op X2 X0) X1)
       grind)
    | exact superpose eq76 eq568
    | exact resolve eq568 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq568
  have eq8861 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) X4) (M.op X1 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7026 X0 (M.op (M.op X0 X1) X2) X2 X0
       have i₂ := eq50 X0 X1 X2
       grind)
    | exact superpose eq50 eq7026
    | exact resolve eq7026 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7026
  have eq9220 : ∀ X0 X2 : G, (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (M.op (M.op (σ y) X2) (M.op (M.op (σ x) X0) (M.op (σ x) X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq8861 (M.op (M.op (σ x) X0) x) (M.op (σ x) X0) x (σ y) X2
       have i₂ := eq384 X0 x
       grind)
    | exact superpose eq384 eq8861
    | exact resolve eq8861 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq8861
  have eq22471 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op y X0) X1) X2) = (M.op (M.op (M.op x X3) (M.op x X3)) (M.op (M.op (M.op y X0) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5664 (M.op (M.op y X0) X1) X1 x x x
       have i₂ := eq238 X0 X1
       grind)
    | exact superpose eq238 eq5664
    | exact resolve eq5664 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq5664
  have eq56034 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j0 := eq214 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq56038 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq878
       have i₂ := eq56034
       grind)
    | exact superpose eq56034 eq878
    | (have r₁ := eq878
       have r₂ := eq56034
       grind)
    | exact resolve eq878 eq56034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq56042 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq56038
  have eq56050 : ∀ X0 : G, y = (M.op x y) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq56042
       grind)
    | exact superpose eq56042 eq9
    | exact resolve eq9 eq56042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56111 : ∀ X0 : G, y = (M.op x y) ∨ (σ x) = (M.op (M.op (M.op (σ y) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2851 (σ x) (σ y) X0
       have i₂ := eq56042
       grind)
    | exact superpose eq56042 eq2851
    | exact resolve eq2851 eq56042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56042
  have eq56215 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq56050 X0
       grind)
    | exact superpose eq56050 eq16
    | (have j1 := eq56050 X0
       grind)
    | exact resolve eq16 eq56050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56216 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y X0) (M.op y X0)) y) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 y X1
       have i₂ := eq56050 X0
       grind)
    | exact superpose eq56050 eq262
    | (have j1 := eq56050 X1
       grind)
    | exact resolve eq262 eq56050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq56241 : ∀ X0 : G, (k (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq58 x y
       have i₂ := eq56050 X0
       grind)
    | exact superpose eq56050 eq58
    | (have j1 := eq56050 X0
       grind)
    | exact resolve eq58 eq56050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq56384 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (M.op (σ y) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq56111 X0
       grind)
    | exact superpose eq56111 eq16
    | (have j1 := eq56111 X0
       grind)
    | exact resolve eq16 eq56111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56111
  have eq59310 : ∀ X1 X2 : G, y = (M.op (M.op (M.op x X2) (M.op x X2)) y) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X1 X2
    first
    | (have i₁ := eq22471 x (M.op y x) y x
       have i₂ := eq56216 x X1
       grind)
    | exact superpose eq56216 eq22471
    | (have j1 := eq56216 x X1
       grind)
    | exact resolve eq22471 eq56216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22471 eq56216
  have eq62338 : ∀ X0 X1 : G, y = (M.op (M.op y y) y) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq59310 X1 y
       have i₂ := eq56050 X0
       grind)
    | exact superpose eq56050 eq59310
    | (have j0 := eq59310 X0 x
       have j1 := eq56050 X0
       grind)
    | exact resolve eq59310 eq56050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59310
  have eq62527 : ∀ X1 : G, y = (M.op (M.op y y) y) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X1
    first
    | (have j0 := eq62338 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62338
  have eq62618 : ∀ X1 : G, y = (M.op (M.op x x) y) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X1
    first
    | (have i₁ := eq62527 X1
       have i₂ := eq222
       grind)
    | exact superpose eq222 eq62527
    | (have j0 := eq62527 X1
       grind)
    | exact resolve eq62527 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62527
  have eq62688 : ∀ X0 : G, x = (M.op (M.op y y) x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq50 x x y
       have i₂ := eq62618 x
       grind)
    | exact superpose eq62618 eq50
    | (have j1 := eq62618 X0
       grind)
    | exact resolve eq50 eq62618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq62723 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op (M.op (M.op (M.op y y) X0) X0) x) X1) x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X2) X2) (σ x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5931 x x y x x
       have i₂ := eq62618 X1
       grind)
    | exact superpose eq62618 eq5931
    | (have j1 := eq62618 X2
       grind)
    | exact resolve eq5931 eq62618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5931 eq62618
  have eq62916 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op (M.op (M.op (M.op x x) X0) X0) x) X1) x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X2) X2) (σ x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62723 X0 X1 X2
       have i₂ := eq222
       grind)
    | exact superpose eq222 eq62723
    | (have j0 := eq62723 X0 X1 X2
       grind)
    | exact resolve eq62723 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62723
  have eq62946 : ∀ X0 : G, x = (M.op (M.op x x) x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq62688 X0
       have i₂ := eq222
       grind)
    | exact superpose eq222 eq62688
    | (have j0 := eq62688 X0
       grind)
    | exact resolve eq62688 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq62688
  have eq63006 : ∀ X1 X2 : G, x = (M.op (M.op x X1) x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X2) X2) (σ x)) := by
    intro X1 X2
    first
    | (have i₁ := eq62916 x X1 X2
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq62916
    | (have j0 := eq62916 x X1 X2
       grind)
    | exact resolve eq62916 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62916
  have eq64794 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (k (M.op x X0) x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2930 x x x
       have i₂ := eq62946 X0
       grind)
    | exact superpose eq62946 eq2930
    | (have j1 := eq62946 X1
       grind)
    | exact resolve eq2930 eq62946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930 eq62946
  have eq65034 : ∀ X0 X1 : G, (M.op x X0) = (k (M.op x X0) x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq64794 X0 X1
       have i₂ := eq46 x X0
       grind)
    | exact superpose eq46 eq64794
    | (have j0 := eq64794 X0 X1
       grind)
    | exact resolve eq64794 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64794
  have eq65093 : ∀ X0 X1 : G, x = (M.op y x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq63006 y X0
       have i₂ := eq56050 X1
       grind)
    | exact superpose eq56050 eq63006
    | (have j0 := eq63006 X1 X0
       have j1 := eq56050 X0
       grind)
    | exact resolve eq63006 eq56050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63006
  have eq65335 : ∀ X1 : G, x = (M.op y x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X1
    first
    | (have j0 := eq65093 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65093
  have eq65472 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq56241 X0
       have i₂ := eq65335 X1
       grind)
    | exact superpose eq65335 eq56241
    | (have j0 := eq56241 X0
       have j1 := eq65335 X0
       grind)
    | exact resolve eq56241 eq65335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56241 eq65335
  have eq65625 : ∀ X1 : G, (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X1
    first
    | (have j0 := eq65472 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65472
  have eq66140 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq56034
       have i₂ := eq65625 X0
       grind)
    | exact superpose eq65625 eq56034
    | (have j1 := eq65625 X0
       grind)
    | exact resolve eq56034 eq65625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56034 eq65625
  have eq66149 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq66140 X0
       have j1 := eq56215 X0
       grind)
    | (have r₁ := eq66140 X0
       have r₂ := eq56215 X0
       grind)
    | exact resolve eq66140 eq56215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56215 eq66140
  have eq66212 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq46 (σ x) (σ y)
       have i₂ := eq66149 X0
       grind)
    | exact superpose eq66149 eq46
    | (have j1 := eq66149 X0
       grind)
    | exact resolve eq46 eq66149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq67381 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq205
       have i₂ := eq66212 X0
       grind)
    | exact superpose eq66212 eq205
    | (have j1 := eq66212 X0
       grind)
    | exact resolve eq205 eq66212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq66212
  have eq68095 : ∀ X0 : G, (k (τ (σ y)) (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq57 (σ y) (σ x)
       have i₂ := eq67381 X0
       grind)
    | exact superpose eq67381 eq57
    | (have j1 := eq67381 X0
       grind)
    | exact resolve eq57 eq67381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67381
  have eq68204 : ∀ X0 : G, (k (τ (σ y)) x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq68095 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq68095
    | (have j0 := eq68095 X0
       grind)
    | exact resolve eq68095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68095
  have eq68205 : ∀ X0 : G, (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq68204 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq68204
    | (have j0 := eq68204 X0
       grind)
    | exact resolve eq68204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68204
  have eq68544 : ∀ X0 X1 : G, y = (k y x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq65034 y X1
       have i₂ := eq56050 X0
       grind)
    | exact superpose eq56050 eq65034
    | (have j0 := eq65034 X0 X0
       have j1 := eq56050 X0
       grind)
    | exact resolve eq65034 eq56050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56050 eq65034
  have eq68561 : ∀ X1 : G, y = (k y x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X1
    first
    | (have j0 := eq68544 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68544
  have eq74255 : ∀ X0 X1 : G, (k y x) = (τ (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq68205 X0
       have i₂ := eq66149 X1
       grind)
    | exact superpose eq66149 eq68205
    | (have j0 := eq68205 X0
       have j1 := eq66149 X0
       grind)
    | exact resolve eq68205 eq66149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66149 eq68205
  have eq74266 : ∀ X1 : G, (k y x) = (τ (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X1
    first
    | (have j0 := eq74255 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74255
  have eq74271 : ∀ X1 : G, x = (k y x) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X1
    first
    | (have i₁ := eq74266 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq74266
    | (have j0 := eq74266 X1
       grind)
    | exact resolve eq74266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74266
  have eq74279 : ∀ X0 X1 : G, x = y ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq68561 X0
       have i₂ := eq74271 X1
       grind)
    | exact superpose eq74271 eq68561
    | (have j0 := eq68561 X0
       have j1 := eq74271 X0
       grind)
    | exact resolve eq68561 eq74271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68561 eq74271
  have eq74288 : ∀ X1 : G, x = y ∨ (σ x) = (M.op (M.op (M.op (σ y) X1) X1) (σ x)) := by
    intro X1
    first
    | (have j0 := eq74279 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74279
  have eq74292 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq74288 x
       grind)
    | exact superpose eq74288 eq16
    | (have j1 := eq74288 X0
       grind)
    | exact resolve eq16 eq74288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74288
  have eq74584 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq74292 X0
       grind)
    | (have r₁ := eq74292 X0
       have r₂ := eq108 x
       grind)
    | exact resolve eq74292 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74292
  have eq74640 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9 (σ y) (σ x) (σ x)
       have i₂ := eq74584 (σ x)
       grind)
    | exact superpose eq74584 eq9
    | exact resolve eq9 eq74584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74645 : (τ (M.op (σ y) (σ x))) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq335 (σ x) (σ x) (σ y)
       have i₂ := eq74584 (σ x)
       grind)
    | exact superpose eq74584 eq335
    | exact resolve eq335 eq74584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq74584
  have eq74859 : (τ (M.op (σ y) (σ x))) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq74645
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq74645
    | exact resolve eq74645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74645
  have eq74861 : (k x y) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq74859
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq74859
    | exact resolve eq74859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74859
  have eq74865 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ y) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq56384 X0
       grind)
    | (have r₁ := eq56384 X0
       have r₂ := eq74640
       grind)
    | exact resolve eq56384 eq74640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56384
  have eq75064 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq74865 (M.op (M.op (σ x) X0) (M.op (σ x) X0))
       have i₂ := eq9220 X0 (σ x)
       grind)
    | exact superpose eq9220 eq74865
    | exact resolve eq74865 eq9220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9220 eq74865
  have eq76218 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq75064 (σ y)
       have i₂ := eq74640
       grind)
    | exact superpose eq74640 eq75064
    | exact resolve eq75064 eq74640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75064
  have eq76423 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq76218
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq76218
    | exact resolve eq76218 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq76218
  have eq76432 : (τ (σ x)) = (k (τ (σ x)) (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq57 (σ x) (σ x)
       have i₂ := eq76423
       grind)
    | exact superpose eq76423 eq57
    | exact resolve eq57 eq76423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq76436 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2851 (σ x) (σ x) X0
       have i₂ := eq76423
       grind)
    | exact superpose eq76423 eq2851
    | exact resolve eq2851 eq76423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76423
  have eq76739 : (τ (σ x)) = (k (τ (σ x)) (M.op x x)) := by
    first
    | (have i₁ := eq76432
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq76432
    | exact resolve eq76432 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq76432
  have eq76761 : x = (k x (M.op x x)) := by
    first
    | (have i₁ := eq76739
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq76739
    | exact resolve eq76739 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76739
  have eq76768 : x = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq76761
       have i₂ := eq53 x x
       grind)
    | exact superpose eq53 eq76761
    | exact resolve eq76761 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq76761
  have eq76773 : y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq224 x
       have i₂ := eq76768
       grind)
    | exact superpose eq76768 eq224
    | exact resolve eq224 eq76768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq76791 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq2851 x x X0
       have i₂ := eq76768
       grind)
    | exact superpose eq76768 eq2851
    | exact resolve eq2851 eq76768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2851 eq76768
  have eq78274 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq76436 (σ y)
       have i₂ := eq74640
       grind)
    | exact superpose eq74640 eq76436
    | exact resolve eq76436 eq74640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76436
  have eq78587 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq74861
       have i₂ := eq78274
       grind)
    | exact superpose eq78274 eq74861
    | exact resolve eq74861 eq78274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74861 eq78274
  have eq78742 : x = (k x y) := by
    first
    | (have i₁ := eq78587
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq78587
    | exact resolve eq78587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78587
  have eq78762 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78742
       have i₂ := eq864
       grind)
    | exact superpose eq864 eq78742
    | exact resolve eq78742 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq78742
  have eq79352 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78762
       grind)
    | exact superpose eq78762 eq16
    | exact resolve eq16 eq78762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78762
  have eq79503 : x = (M.op x y) := by
    first
    | (have r₁ := eq79352
       have r₂ := eq74640
       grind)
    | exact resolve eq79352 eq74640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74640 eq79352
  have eq79552 : x = (M.op x x) := by
    first
    | (have i₁ := eq76791 y
       have i₂ := eq79503
       grind)
    | exact superpose eq79503 eq76791
    | exact resolve eq76791 eq79503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76791
  have eq79701 : y = (M.op x y) := by
    first
    | (have i₁ := eq76773
       have i₂ := eq79552
       grind)
    | exact superpose eq79552 eq76773
    | exact resolve eq76773 eq79552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76773 eq79552
  have eq79834 : x = y := by
    first
    | (have i₁ := eq79701
       have i₂ := eq79503
       grind)
    | exact superpose eq79503 eq79701
    | exact resolve eq79701 eq79503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79503 eq79701
  have eq79847 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79834
       grind)
    | exact superpose eq79834 eq16
    | exact resolve eq16 eq79834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79834
  have eq80039 : False := by grind
  exact eq80039
