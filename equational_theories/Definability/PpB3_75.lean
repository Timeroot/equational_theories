import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq68 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq297 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq298 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq300 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq301 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq304 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq299 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq299 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq299 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq315 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq304 (σ X0)
       grind)
    | exact superpose eq304 eq15
    | exact resolve eq15 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq304 X0
       grind)
    | exact superpose eq304 eq315
    | exact resolve eq315 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq315
  have eq378 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq68
    | exact resolve eq68 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq378
    | exact resolve eq378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq389 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq387
    | exact resolve eq387 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq387
  have eq422 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq301 (τ X1) X0
       grind)
    | exact superpose eq301 eq19
    | (have j1 := eq301 (τ X1) X0
       grind)
    | exact resolve eq19 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq425 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq301 (σ X1) (σ X0)
       grind)
    | exact superpose eq301 eq15
    | (have j1 := eq301 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq448 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X1
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq425
    | (have j0 := eq425 X0 X1
       grind)
    | exact resolve eq425 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq425
  have eq715 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq422 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq422
    | exact resolve eq422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq770 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq715
    | (have j0 := eq715 X0 X1
       grind)
    | exact resolve eq715 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq1242 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq448 x y
       grind)
    | exact superpose eq448 eq16
    | (have j1 := eq448 x y
       grind)
    | exact resolve eq16 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq1324 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1242
       have i₂ := eq770 y x
       grind)
    | exact superpose eq770 eq1242
    | (have j1 := eq770 y x
       grind)
    | (have r₁ := eq1242
       have r₂ := eq770 y x
       grind)
    | exact resolve eq1242 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq1242
  have eq1325 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1324
  have eq1335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq389 x
       have i₂ := eq1325
       grind)
    | exact superpose eq1325 eq389
    | exact resolve eq389 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1351 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1335
       have r₂ := eq16
       grind)
    | exact resolve eq1335 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1357 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1351
       grind)
    | exact superpose eq1351 eq10
    | exact resolve eq10 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq1403 : y = (M.op x x) := by
    first
    | (have i₁ := eq1357
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1357
    | exact resolve eq1357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq389 x
       have i₂ := eq1403
       grind)
    | exact superpose eq1403 eq389
    | exact resolve eq389 eq1403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq1403
  have eq1428 : False := by grind
  exact eq1428

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq68 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq297 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq298 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq300 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq301 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq304 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq299 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq299 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq299 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq315 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq304 (σ X0)
       grind)
    | exact superpose eq304 eq15
    | exact resolve eq15 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq304 X0
       grind)
    | exact superpose eq304 eq315
    | exact resolve eq315 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq315
  have eq378 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq68
    | exact resolve eq68 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq378
    | exact resolve eq378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq389 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq387
    | exact resolve eq387 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq387
  have eq422 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq301 (τ X1) X0
       grind)
    | exact superpose eq301 eq19
    | (have j1 := eq301 (τ X1) X0
       grind)
    | exact resolve eq19 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq425 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq301 (σ X1) (σ X0)
       grind)
    | exact superpose eq301 eq15
    | (have j1 := eq301 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq448 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X1
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq425
    | (have j0 := eq425 X0 X1
       grind)
    | exact resolve eq425 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq425
  have eq715 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq422 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq422
    | exact resolve eq422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq770 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq715
    | (have j0 := eq715 X0 X1
       grind)
    | exact resolve eq715 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq1242 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq448 x y
       grind)
    | exact superpose eq448 eq16
    | (have j1 := eq448 x y
       grind)
    | exact resolve eq16 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq1325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1242
       have i₂ := eq770 y x
       grind)
    | exact superpose eq770 eq1242
    | (have j1 := eq770 y x
       grind)
    | (have r₁ := eq1242
       have r₂ := eq770 y x
       grind)
    | exact resolve eq1242 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq1242
  have eq1326 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1325
  have eq1336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq389 x
       have i₂ := eq1326
       grind)
    | exact superpose eq1326 eq389
    | exact resolve eq389 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1352 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1336
       have r₂ := eq16
       grind)
    | exact resolve eq1336 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1358 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1352
       grind)
    | exact superpose eq1352 eq10
    | exact resolve eq10 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1404 : y = (M.op x x) := by
    first
    | (have i₁ := eq1358
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1358
    | exact resolve eq1358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1413 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq389 x
       have i₂ := eq1404
       grind)
    | exact superpose eq1404 eq389
    | exact resolve eq389 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq1404
  have eq1429 : False := by grind
  exact eq1429

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq26 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq37 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq76 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq77 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76
    | (have j0 := eq76 X0
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq65 X1 X0 X3
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq433 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq453 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq10
    | (have j1 := eq69 X0
       grind)
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq484 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq26
    | (have j1 := eq77 X0
       grind)
    | exact resolve eq26 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq10
    | (have j1 := eq77 X0
       grind)
    | exact resolve eq10 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq508 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (k (τ X0) (τ X0))
       have i₂ := eq484 (τ X0)
       grind)
    | exact superpose eq484 eq20
    | (have j1 := eq484 (τ X0)
       grind)
    | exact resolve eq20 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq484
  have eq513 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq508 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq508
    | (have j0 := eq508 X0
       grind)
    | exact resolve eq508 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq508
  have eq529 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq513 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq513
    | (have j0 := eq513 X0
       grind)
    | exact resolve eq513 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq679 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq66 (τ X0)
       have i₂ := eq490 X0
       grind)
    | exact superpose eq490 eq66
    | (have j1 := eq490 X0
       grind)
    | exact resolve eq66 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq683 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq490 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq692 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq683 (σ X0)
       have i₂ := eq31 X0 (σ X0)
       grind)
    | exact superpose eq31 eq683
    | (have j0 := eq683 (σ X0)
       grind)
    | exact resolve eq683 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq693 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq692 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq692
    | (have j0 := eq692 X0
       grind)
    | exact resolve eq692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq696 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq693 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq693
    | (have j0 := eq693 X0
       grind)
    | exact resolve eq693 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq701 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq696 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq696
    | (have j0 := eq696 (σ X0)
       grind)
    | exact resolve eq696 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3210 : ∀ X0 : G, (σ (τ (τ X0))) = (k (σ (τ (τ X0))) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq26 (τ X0)
       have i₂ := eq529 X0
       grind)
    | exact superpose eq529 eq26
    | (have j1 := eq529 X0
       grind)
    | exact resolve eq26 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq529
  have eq3217 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3210 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq3210
    | (have j0 := eq3210 X0
       grind)
    | exact resolve eq3210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3210
  have eq3220 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3217 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq3217
    | (have j0 := eq3217 X0
       grind)
    | exact resolve eq3217 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3217
  have eq3241 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (k (σ X0) (σ X0)) X0
       have i₂ := eq3220 (σ X0)
       grind)
    | exact superpose eq3220 eq24
    | (have j1 := eq3220 (σ X0)
       grind)
    | exact resolve eq24 eq3220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3220
  have eq3288 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3241 x
       have i₂ := eq24 (σ x) x
       grind)
    | exact superpose eq24 eq3241
    | (have j0 := eq3241 X0
       grind)
    | exact resolve eq3241 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3241
  have eq3328 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3288 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3288
    | (have j0 := eq3288 X0
       grind)
    | exact resolve eq3288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288
  have eq3365 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3328 X0
       have i₂ := eq24 (σ X0) X0
       grind)
    | exact superpose eq24 eq3328
    | (have j0 := eq3328 X0
       grind)
    | exact resolve eq3328 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3328
  have eq3401 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3365 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3365
    | (have j0 := eq3365 X0
       grind)
    | exact resolve eq3365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3474 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq3401 X0
       grind)
    | exact superpose eq3401 eq14
    | (have j0 := eq14 (k X0 X0) X0
       have j1 := eq3401 X0
       grind)
    | exact resolve eq14 eq3401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3401
  have eq3499 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3474 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474
  have eq4645 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3499 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq3499
    | exact resolve eq3499 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3499
  have eq4657 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | exact superpose eq679 eq4645
    | (have j0 := eq4645 X0
       have j1 := eq679 X0
       grind)
    | exact resolve eq4645 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq4645
  have eq4658 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4657 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq4677 : ∀ X0 : G, (k X0 (τ (σ X0))) = (M.op (k X0 (τ (σ X0))) (τ (σ X0))) ∨ (τ (σ X0)) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4658 (σ X0)
       have i₂ := eq31 X0 (σ X0)
       grind)
    | exact superpose eq31 eq4658
    | exact resolve eq4658 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4658
  have eq4723 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (τ (σ X0)) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4677 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4677
    | (have j0 := eq4677 X0
       grind)
    | exact resolve eq4677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4677
  have eq4742 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4723 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4723
    | (have j0 := eq4723 X0
       grind)
    | exact resolve eq4723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723
  have eq4780 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4742 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq4742
    | exact resolve eq4742 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4742
  have eq4803 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq4780
  have eq9062 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq81
    | (have j0 := eq81 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq81 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq12079 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq94 x X2 X0 X1
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq12118 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12079 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq12079 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq12079 eq12079
    | exact resolve eq12079 eq12079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12079
  have eq41723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9062 x y
       grind)
    | exact superpose eq9062 eq16
    | (have j1 := eq9062 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq9062 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq9062 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq9062 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq9062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9062
  have eq41772 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq41723
  have eq41880 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq453 y
       have i₂ := eq41772
       grind)
    | exact superpose eq41772 eq453
    | exact resolve eq453 eq41772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq41772
  have eq41932 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq41880
  have eq41966 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41932
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41932
    | exact resolve eq41932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41932
  have eq42010 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  have eq42092 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq42010
  have eq42140 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq42092
  have eq42197 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq41966 eq42140
    | exact resolve eq42140 eq41966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41966 eq42140
  have eq42198 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq42197
  have eq42223 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4803 y
       have i₂ := eq42198
       grind)
    | exact superpose eq42198 eq4803
    | exact resolve eq4803 eq42198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq42226 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12118 y y
       have i₂ := eq42198
       grind)
    | exact superpose eq42198 eq12118
    | exact resolve eq12118 eq42198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12118 eq42198
  have eq42261 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq42223
  have eq42585 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq42261
       grind)
    | exact superpose eq42261 eq16
    | exact resolve eq16 eq42261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42261
  have eq42669 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq42226 eq42585
    | exact resolve eq42585 eq42226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42226 eq42585
  have eq42670 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq42669
  have eq42726 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq42670
       grind)
    | exact superpose eq42670 eq10
    | exact resolve eq10 eq42670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42670
  have eq42898 : x = y ∨ x = y := by
    first
    | (have i₁ := eq42726
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq42726
    | exact resolve eq42726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42726
  have eq42899 : x = y := by grind
  clear eq42898
  have eq42900 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42899
       grind)
    | exact superpose eq42899 eq16
    | exact resolve eq16 eq42899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42899
  have eq42901 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq42900
       have i₂ := eq433 x
       grind)
    | exact superpose eq433 eq42900
    | (have j1 := eq433 x
       grind)
    | (have r₁ := eq42900
       have r₂ := eq433 x
       grind)
    | exact resolve eq42900 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq42902 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq42901
  have eq43174 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq42902
       grind)
    | exact superpose eq42902 eq37
    | exact resolve eq37 eq42902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq42902
  have eq43236 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43174
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq43174
    | exact resolve eq43174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43174
  have eq43248 : x = (M.op x x) := by
    first
    | (have j1 := eq696 x
       grind)
    | (have r₁ := eq43236
       have r₂ := eq696 x
       grind)
    | exact resolve eq43236 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq43236
  have eq43271 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq42900
       have i₂ := eq43248
       grind)
    | exact superpose eq43248 eq42900
    | exact resolve eq42900 eq43248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42900
  have eq43272 : x = (k x x) := by grind
  clear eq43248
  have eq43334 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq701 x
       have i₂ := eq43272
       grind)
    | exact superpose eq43272 eq701
    | (have j0 := eq701 x
       grind)
    | exact resolve eq701 eq43272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq43272
  have eq43342 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq43334
  have eq43350 : False := by grind
  exact eq43350

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq44 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq44 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq45 (σ X0)
       grind)
    | exact superpose eq45 eq15
    | exact resolve eq15 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq47
    | exact resolve eq47 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq52
    | exact resolve eq52 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq54 X1
       grind)
    | exact superpose eq54 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq90 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq54
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq20
    | exact resolve eq20 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq10
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq150 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (τ X0)
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq20
    | exact resolve eq20 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq157 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq86
    | (have j0 := eq86 X0 X2
       grind)
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq183 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq159 X0 X1 X2
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq159
    | (have j0 := eq159 X0 X1 X2
       grind)
    | exact resolve eq159 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq159
  have eq185 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq157
    | (have j0 := eq157 X0 X1
       grind)
    | exact resolve eq157 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq189 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq185 X0 X0
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq185 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq193 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq189
    | (have j0 := eq189 X0 X1
       grind)
    | exact resolve eq189 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq198 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq93 (σ X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq93
    | exact resolve eq93 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq221 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op X0 X0))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq150 (τ X0)
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq150
    | exact resolve eq150 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq517 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
  clear eq193
  have eq564 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq517 X1 (σ X0)
       grind)
    | exact superpose eq517 eq32
    | (have j1 := eq517 X1 (σ X0)
       grind)
    | exact resolve eq32 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq575 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq564
    | (have j0 := eq564 X0 X1
       grind)
    | exact resolve eq564 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq912 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq118 x X2 X0 X1
       grind)
    | exact superpose eq118 eq9
    | exact resolve eq9 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq951 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq912 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq912 eq9
    | exact resolve eq9 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1683 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k (k (σ X0) X1) X3) ∨ (M.op X3 X3) = X3 ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq183 X0 X1 X2
       grind)
    | exact superpose eq183 eq13
    | (have j0 := eq13 X0 X3
       have j1 := eq183 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq183 X0 X1 X2
       grind)
    | exact resolve eq13 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq2644 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq575 X0 (M.op X1 (M.op X2 (σ (M.op X0 X0))))
       have i₂ := eq94 X0 X1 X2
       grind)
    | exact superpose eq94 eq575
    | exact resolve eq575 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq575
  have eq2686 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2644 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2644
    | (have j0 := eq2644 X0 X1 X2
       grind)
    | exact resolve eq2644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2644
  have eq2796 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq912 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq951 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq951 eq912
    | exact resolve eq912 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912 eq951
  have eq2972 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 X0
       have i₂ := eq2796 X1 X2 X0
       grind)
    | exact superpose eq2796 eq9
    | exact resolve eq9 eq2796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2796
  have eq3255 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ (σ X0)))) = (M.op (M.op X1 (M.op X2 (σ (σ X0)))) (σ (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2972 (σ (σ X0)) X1 X2 (σ (σ (M.op X0 X0)))
       have i₂ := eq198 X0
       grind)
    | exact superpose eq198 eq2972
    | exact resolve eq2972 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq2972
  have eq16723 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq2686 X0 X1 X2
       grind)
    | exact superpose eq2686 eq10
    | (have j1 := eq2686 X0 X1 X2
       grind)
    | exact resolve eq10 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686
  have eq16817 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16723 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16723
    | (have j0 := eq16723 X0 X1 X2
       grind)
    | exact resolve eq16723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16723
  have eq16934 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ X0)))))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (τ (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ X0))))))
       have i₂ := eq16817 (τ X0) X1 X2
       grind)
    | exact superpose eq16817 eq17
    | (have j1 := eq16817 (τ X0) X1 X2
       grind)
    | exact resolve eq17 eq16817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq16817
  have eq17016 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ X0)))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16934 X0 X1 X2
       have i₂ := eq11 (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ X0)))))
       grind)
    | exact superpose eq11 eq16934
    | (have j0 := eq16934 X0 X1 X2
       grind)
    | exact resolve eq16934 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16934
  have eq17073 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17016 X0 X1 X2
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq17016
    | (have j0 := eq17016 X0 X1 X2
       grind)
    | exact resolve eq17016 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq17016
  have eq17125 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17073 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17073
    | (have j0 := eq17073 X0 X1 X2
       grind)
    | exact resolve eq17073 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17073
  have eq17162 : ∀ X0 X1 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17125 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq17125
    | (have j0 := eq17125 X0 X1 X2
       grind)
    | exact resolve eq17125 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17125
  have eq17515 : ∀ X0 X1 X2 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq221 X0
       have i₂ := eq17162 X0 X1 X2
       grind)
    | exact superpose eq17162 eq221
    | (have j1 := eq17162 X0 X1 X2
       grind)
    | exact resolve eq221 eq17162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq17162
  have eq17680 : ∀ X0 X1 X2 : G, (τ (M.op (τ X0) (τ X0))) = (τ (τ X0)) ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17515 X0 X1 X2
       have i₂ := eq106 (τ X0)
       grind)
    | exact superpose eq106 eq17515
    | (have j0 := eq17515 X0 X1 X2
       grind)
    | exact resolve eq17515 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17515
  have eq17688 : ∀ X0 X1 X2 : G, (τ (τ X0)) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17680 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq17680
    | (have j0 := eq17680 X0 X1 X2
       grind)
    | exact resolve eq17680 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq17680
  have eq31736 : ∀ X0 X1 X2 : G, (τ (τ (σ X0))) = (τ (τ (σ (M.op X0 X0)))) ∨ (σ X0) = (k (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17688 (σ X0) X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq17688
    | exact resolve eq17688 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17688
  have eq31962 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (τ (σ X0))) ∨ (σ X0) = (k (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31736 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq31736
    | (have j0 := eq31736 X0 X1 X2
       grind)
    | exact resolve eq31736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31736
  have eq31972 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31962 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31962
    | (have j0 := eq31962 X0 X1 X2
       grind)
    | exact resolve eq31962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31962
  have eq50435 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 (M.op X1 (M.op X2 (σ (M.op X0 X0))))
       have i₂ := eq31972 X0 X1 X2
       grind)
    | exact superpose eq31972 eq32
    | (have j1 := eq31972 X0 X1 X2
       grind)
    | exact resolve eq32 eq31972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31972
  have eq50491 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50435 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50435
    | (have j0 := eq50435 X0 X1 X2
       grind)
    | exact resolve eq50435 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50435
  have eq50948 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op X2 (σ (M.op (σ X0) (σ X0)))))))) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 (τ (M.op X1 (M.op X2 (σ (M.op (σ X0) (σ X0))))))
       have i₂ := eq50491 (σ X0) X1 X2
       grind)
    | exact superpose eq50491 eq32
    | (have j1 := eq50491 (σ X0) X1 X2
       grind)
    | exact resolve eq32 eq50491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq50491
  have eq51084 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50948 X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq50948
    | (have j0 := eq50948 X0 X1 X2
       grind)
    | exact resolve eq50948 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50948
  have eq51165 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) = X0 ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51084 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51084
    | (have j0 := eq51084 X0 X1 X2
       grind)
    | exact resolve eq51084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51084
  have eq51235 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51165 X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq51165
    | (have j0 := eq51165 X0 X1 X2
       grind)
    | exact resolve eq51165 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51165
  have eq51283 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51235 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq51235
    | (have j0 := eq51235 X0 X1 X2
       grind)
    | exact resolve eq51235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51235
  have eq51320 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51283 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51283
    | (have j0 := eq51283 X0 X1 X2
       grind)
    | exact resolve eq51283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51283
  have eq51880 : ∀ X0 X1 X2 X3 : G, (k X2 (τ (τ (M.op X3 (M.op X0 (M.op X1 (σ (σ X2)))))))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51320 X2 X3 (M.op X0 (M.op X1 (σ (σ X2))))
       have i₂ := eq3255 X2 X0 X1
       grind)
    | exact superpose eq3255 eq51320
    | (have j0 := eq51320 X2 X1 X2
       grind)
    | exact resolve eq51320 eq3255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3255 eq51320
  have eq80360 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1683 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq80363 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq80360 X0 X1 X2
       have j1 := eq12 (k (σ X0) X1) (σ X2)
       grind)
    | (have r₁ := eq80360 X0 X1 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | exact resolve eq80360 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80360
  have eq80458 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq80363 X0 X1 X2
       have j1 := eq92 X2 (k (σ X0) X1)
       grind)
    | (have r₁ := eq80363 X0 X1 X0
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq80363 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq80363
  have eq80527 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80458 X0 X1 X2
       have i₂ := eq31 X0 X1 X2
       grind)
    | exact superpose eq31 eq80458
    | (have j0 := eq80458 X0 X1 X2
       grind)
    | exact resolve eq80458 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq80458
  have eq80528 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq80527 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80527
  have eq80623 : ∀ X0 X1 X2 : G, (M.op (k (σ X1) (σ X0)) (σ X2)) = (σ (k (k X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80528 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80528
    | exact resolve eq80528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80792 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k X0 (τ X1))
       have i₂ := eq80528 X0 X1 (τ X2)
       grind)
    | exact superpose eq80528 eq18
    | exact resolve eq18 eq80528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80528
  have eq80954 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80792 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq80792
    | exact resolve eq80792 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80792
  have eq81066 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (M.op (σ (k X1 X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80623 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq80623
    | exact resolve eq80623 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80623
  have eq81092 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) X2) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80954 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq80954
    | exact resolve eq80954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq80954
  have eq81257 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81092 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81092
    | exact resolve eq81092 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81318 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) X1) = (M.op (M.op (σ X0) (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81092 X0 (σ X0) x
       have i₂ := eq45 (σ X0)
       grind)
    | exact superpose eq45 eq81092
    | exact resolve eq81092 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81092
  have eq81644 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81318 X0 X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq81318
    | exact resolve eq81318 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq81318
  have eq82401 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81257 X0 X0 x
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq81257
    | exact resolve eq81257 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq82443 : ∀ X0 X4 : G, (k X0 X4) = (M.op X0 X4) ∨ (M.op X0 X0) = X0 := by
    intro X0 X4
    first
    | (have i₁ := eq81257 x (τ (τ (M.op x (M.op X0 (M.op x (σ (σ x))))))) x
       have i₂ := eq51880 X0 x x x
       grind)
    | exact superpose eq51880 eq81257
    | (have j1 := eq51880 X0 x X0 x
       grind)
    | exact resolve eq81257 eq51880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81257
  have eq87551 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq81644 X0 (σ X1)
       grind)
    | exact superpose eq81644 eq15
    | exact resolve eq15 eq81644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81644
  have eq87722 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87551 X0 X1
       have i₂ := eq82401 X0 X1
       grind)
    | exact superpose eq82401 eq87551
    | exact resolve eq87551 eq82401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82401 eq87551
  have eq89452 : ∀ X0 X4 : G, (σ (k X0 X4)) = (M.op (σ X0) (σ X4)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X4
    first
    | (have i₁ := eq81066 (τ (τ (M.op x (M.op X0 (M.op x (σ (σ x))))))) x x
       have i₂ := eq51880 X0 x x x
       grind)
    | exact superpose eq51880 eq81066
    | (have j1 := eq51880 X0 x X0 x
       grind)
    | exact resolve eq81066 eq51880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51880 eq81066
  have eq124883 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89452 x y
       grind)
    | exact superpose eq89452 eq16
    | (have j1 := eq89452 x x
       grind)
    | exact resolve eq16 eq89452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89452
  have eq128135 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq124883
       have i₂ := eq82443 x y
       grind)
    | exact superpose eq82443 eq124883
    | (have j1 := eq82443 x x
       grind)
    | exact resolve eq124883 eq82443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82443 eq124883
  have eq128146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq128135
  have eq128147 : x = (M.op x x) := by grind
  clear eq128146
  have eq128252 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq87722 x x
       have i₂ := eq128147
       grind)
    | exact superpose eq128147 eq87722
    | exact resolve eq87722 eq128147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87722 eq128147
  have eq142317 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128252 y
       grind)
    | exact superpose eq128252 eq16
    | (have r₁ := eq16
       have r₂ := eq128252 y
       grind)
    | exact resolve eq16 eq128252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128252
  have eq142657 : False := by grind
  exact eq142657

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq39 X1 X0
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq41 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq41
  have eq49 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq46
  have eq106 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq110 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       have j1 := eq49 X0 X1
       grind)
    | (have r₁ := eq106 X0 X1
       have r₂ := eq49 X0 X1
       grind)
    | (have r₁ := eq106 X1 X1
       have r₂ := eq49 X1 X1
       grind)
    | exact resolve eq106 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq106
  have eq246 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq110 (σ X0) (σ X1)
       grind)
    | exact superpose eq110 eq15
    | exact resolve eq15 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 X0 X1
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq246
    | exact resolve eq246 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq246
  have eq256 : False := by grind
  exact eq256

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq71 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq105 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 x y
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 x y
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq69 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq69 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq304 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq334 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq304
    | (have j0 := eq304 X1 X1
       grind)
    | exact resolve eq304 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq668 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq80 x X2 X0 X1
       grind)
    | exact superpose eq80 eq9
    | exact resolve eq9 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq694 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq668 x X1 X0
       grind)
    | exact superpose eq668 eq9
    | exact resolve eq9 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq733 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq105
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq734 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq733
  have eq2329 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq334 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq2330 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2329 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329
  have eq2350 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq2330 X0
       grind)
    | exact superpose eq2330 eq10
    | (have j1 := eq2330 X0
       grind)
    | exact resolve eq10 eq2330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330
  have eq2398 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2350 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2350
    | (have j0 := eq2350 X0
       grind)
    | exact resolve eq2350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2404 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2398 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq2398 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq2398 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq2410 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq2404 X0
       grind)
    | exact superpose eq2404 eq121
    | (have j0 := eq121 X0 X1
       grind)
    | exact resolve eq121 eq2404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2433 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq112 X0 X0
       have i₂ := eq2404 X0
       grind)
    | exact superpose eq2404 eq112
    | (have j0 := eq112 X0 X0
       grind)
    | exact resolve eq112 eq2404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq2442 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2404 (σ X0)
       grind)
    | exact superpose eq2404 eq15
    | exact resolve eq15 eq2404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2456 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2433 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433
  have eq2469 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2442 X0
       have i₂ := eq2404 X0
       grind)
    | exact superpose eq2404 eq2442
    | exact resolve eq2442 eq2404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2404 eq2442
  have eq18859 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq694 y x
       have i₂ := eq734
       grind)
    | exact superpose eq734 eq694
    | exact resolve eq694 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq18873 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18859
  have eq18892 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq18873
       have i₂ := eq2469 y
       grind)
    | exact superpose eq2469 eq18873
    | exact resolve eq18873 eq2469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18873
  have eq18911 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq694 (σ y) (σ x)
       have i₂ := eq18892
       grind)
    | exact superpose eq18892 eq694
    | exact resolve eq694 eq18892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq18892
  have eq18927 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq2456 y
       grind)
    | (have r₁ := eq18911
       have r₂ := eq2456 y
       grind)
    | exact resolve eq18911 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2456 eq18911
  have eq18931 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18927
       have i₂ := eq2469 y
       grind)
    | exact superpose eq2469 eq18927
    | exact resolve eq18927 eq2469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469 eq18927
  have eq18950 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq18931
       grind)
    | exact superpose eq18931 eq10
    | exact resolve eq10 eq18931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18931
  have eq19041 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18950
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq18950
    | exact resolve eq18950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18950
  have eq19042 : y = (M.op y y) := by grind
  clear eq19041
  have eq19192 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq19042
       grind)
    | exact superpose eq19042 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq19042
       grind)
    | exact resolve eq12 eq19042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19202 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2410 y X0
       have i₂ := eq19042
       grind)
    | exact superpose eq19042 eq2410
    | (have j0 := eq2410 y X0
       grind)
    | exact resolve eq2410 eq19042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410 eq19042
  have eq19249 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq19202 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19202
  have eq19250 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq19192 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19192
  have eq20470 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq19249 (σ X0)
       grind)
    | exact superpose eq19249 eq15
    | exact resolve eq15 eq19249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19249
  have eq20551 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq20470 X0
       have i₂ := eq19250 X0
       grind)
    | exact superpose eq19250 eq20470
    | exact resolve eq20470 eq19250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19250 eq20470
  have eq22770 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20551 x
       grind)
    | exact superpose eq20551 eq16
    | (have r₁ := eq16
       have r₂ := eq20551 x
       grind)
    | exact resolve eq16 eq20551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20551
  have eq22847 : False := by grind
  exact eq22847

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq61 X1 X0 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq284 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq284 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq287 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq285 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq285 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq285 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq298 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq287 (σ X0)
       grind)
    | exact superpose eq287 eq15
    | exact resolve eq15 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq287 X0
       grind)
    | exact superpose eq287 eq298
    | exact resolve eq298 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq298
  have eq360 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq360 X0 X1
       have j1 := eq362 X0 X1
       grind)
    | (have r₁ := eq360 X0 X1
       have r₂ := eq362 X0 X1
       grind)
    | exact resolve eq360 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq529 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq367 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq367
    | exact resolve eq367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq367 X1 (σ X0)
       grind)
    | exact superpose eq367 eq15
    | (have j1 := eq367 X1 (σ X0)
       grind)
    | exact resolve eq15 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq610 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq529 X1 (τ X0)
       grind)
    | exact superpose eq529 eq17
    | (have j1 := eq529 X1 (τ X0)
       grind)
    | exact resolve eq17 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq529
  have eq749 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq610 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq610
    | exact resolve eq610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq807 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq749 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq749
    | (have j0 := eq749 X0 X1
       grind)
    | exact resolve eq749 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq1494 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq540 x y
       grind)
    | exact superpose eq540 eq16
    | (have j1 := eq540 x y
       grind)
    | exact resolve eq16 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq1733 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1494
       have i₂ := eq807 x y
       grind)
    | exact superpose eq807 eq1494
    | (have j1 := eq807 (σ x) (σ y)
       grind)
    | (have r₁ := eq1494
       have r₂ := eq807 x y
       grind)
    | exact resolve eq1494 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq1494
  have eq1734 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1733
  have eq31288 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq72 x X2 X0 X1
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq31505 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq31288 x X1 X0
       grind)
    | exact superpose eq31288 eq9
    | exact resolve eq9 eq31288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31288
  have eq31661 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31505 y x
       have i₂ := eq1734
       grind)
    | exact superpose eq1734 eq31505
    | exact resolve eq31505 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq31774 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31505 (σ y) (σ x)
       have i₂ := eq31661
       grind)
    | exact superpose eq31661 eq31505
    | exact resolve eq31505 eq31661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31505 eq31661
  have eq31776 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31774
       have i₂ := eq317 y
       grind)
    | exact superpose eq317 eq31774
    | exact resolve eq31774 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq31774
  have eq31803 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq31776
       grind)
    | exact superpose eq31776 eq10
    | exact resolve eq10 eq31776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31776
  have eq31896 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31803
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq31803
    | exact resolve eq31803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31803
  have eq31897 : y = (M.op y y) := by grind
  clear eq31896
  have eq31906 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq31897
       grind)
    | exact superpose eq31897 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq31897
       grind)
    | exact resolve eq12 eq31897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31914 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq362 y X0
       have i₂ := eq31897
       grind)
    | exact superpose eq31897 eq362
    | (have j0 := eq362 y X0
       grind)
    | exact resolve eq362 eq31897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq31897
  have eq31967 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq31914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31914
  have eq31968 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq31906 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31906
  have eq32735 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq31967 (σ X0)
       grind)
    | exact superpose eq31967 eq15
    | exact resolve eq15 eq31967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31967
  have eq32847 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq32735 X0
       have i₂ := eq31968 X0
       grind)
    | exact superpose eq31968 eq32735
    | exact resolve eq32735 eq31968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31968 eq32735
  have eq34351 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32847 x
       grind)
    | exact superpose eq32847 eq16
    | (have r₁ := eq16
       have r₂ := eq32847 x
       grind)
    | exact resolve eq16 eq32847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32847
  have eq34478 : False := by grind
  exact eq34478

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq290 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq293 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq292 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq292 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq292 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq304 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq293 (σ X0)
       grind)
    | exact superpose eq293 eq15
    | exact resolve eq15 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq293 (τ X0)
       grind)
    | exact superpose eq293 eq32
    | exact resolve eq32 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq317 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq310 X0
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq310
    | exact resolve eq310 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq323 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq304 X0
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq304
    | exact resolve eq304 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq304
  have eq366 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (σ X0)
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq63
    | exact resolve eq63 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       have j1 := eq369 X0 X1
       grind)
    | (have r₁ := eq366 X0 X1
       have r₂ := eq369 X0 X1
       grind)
    | (have r₁ := eq366 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq369 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq366 X0 (σ X0)
       have r₂ := eq369 X0 X1
       grind)
    | exact resolve eq366 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq369
  have eq484 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq374 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq374
    | (have j0 := eq374 (τ X0) X1
       grind)
    | exact resolve eq374 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq374 X1 (σ X0)
       grind)
    | exact superpose eq374 eq15
    | (have j1 := eq374 X1 (σ X0)
       grind)
    | exact resolve eq15 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq517 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq484
    | (have j0 := eq484 X0 X1
       grind)
    | exact resolve eq484 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq484
  have eq518 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq517
    | (have j0 := eq517 X0 X1
       grind)
    | exact resolve eq517 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq541 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq518 X1 (τ X0)
       grind)
    | exact superpose eq518 eq18
    | (have j1 := eq518 X1 (τ X0)
       grind)
    | exact resolve eq18 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq518
  have eq852 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq541 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq541
    | exact resolve eq541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq913 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq852 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq852
    | (have j0 := eq852 X0 X1
       grind)
    | exact resolve eq852 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq1111 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq497 x y
       grind)
    | exact superpose eq497 eq16
    | (have j1 := eq497 x y
       grind)
    | exact resolve eq16 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq1185 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1111
       have i₂ := eq913 x y
       grind)
    | exact superpose eq913 eq1111
    | (have j1 := eq913 x y
       grind)
    | (have r₁ := eq1111
       have r₂ := eq913 x y
       grind)
    | exact resolve eq1111 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq1186 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1185
  have eq1193 : x = y ∨ x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by grind
  have eq1195 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1186
       grind)
    | exact superpose eq1186 eq63
    | exact resolve eq63 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1212 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1193
       grind)
    | exact superpose eq1193 eq16
    | exact resolve eq16 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1213 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1212
       have r₂ := eq323 x
       grind)
    | exact resolve eq1212 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq1212
  have eq1219 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1111
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq1111
    | exact resolve eq1111 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111 eq1213
  have eq1224 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1219
  have eq1226 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1224
       have i₂ := eq1195
       grind)
    | exact superpose eq1195 eq1224
    | exact resolve eq1224 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq1224
  have eq1227 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1226
  have eq1228 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1227
  have eq1235 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq370 y
       have i₂ := eq1228
       grind)
    | exact superpose eq1228 eq370
    | exact resolve eq370 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1236 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1228
       grind)
    | exact superpose eq1228 eq10
    | exact resolve eq10 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1281 : x = (M.op y y) := by
    first
    | (have i₁ := eq1236
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1236
    | exact resolve eq1236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1289 : x = (M.op x y) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq63
    | exact resolve eq63 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1281
  have eq1310 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1235
       grind)
    | exact superpose eq1235 eq16
    | exact resolve eq16 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1317 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1310
       have i₂ := eq1289
       grind)
    | exact superpose eq1289 eq1310
    | exact resolve eq1310 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289 eq1310
  have eq1318 : False := by grind
  exact eq1318
