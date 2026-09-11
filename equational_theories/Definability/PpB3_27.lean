import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq57
  have eq77 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq88
  have eq259 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq271 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq280 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq271 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq294 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq280 X0 X1
       have j1 := eq77 X0 (σ X1)
       grind)
    | (have r₁ := eq280 X0 X1
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq280 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq280
  have eq306 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq294
    | (have j0 := eq294 X0 X1
       grind)
    | exact resolve eq294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq307 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq312 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq307 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq307
    | exact resolve eq307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq307 x y
       grind)
    | exact superpose eq307 eq16
    | exact resolve eq16 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq435 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq312 X0 (τ X1)
       grind)
    | exact superpose eq312 eq17
    | exact resolve eq17 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq312
  have eq452 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq435 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq435
    | exact resolve eq435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq460 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq452
    | exact resolve eq452 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq472 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq324
       have i₂ := eq460 x y
       grind)
    | exact superpose eq460 eq324
    | exact resolve eq324 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq460
  have eq473 : False := by grind
  exact eq473

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq58 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq24
  have eq59 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58
    | (have j0 := eq58 X0
       grind)
    | exact resolve eq58 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = X0 := by
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
  clear eq18
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq54 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq54 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq54 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq90 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq86 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq86 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq197 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq372 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X1 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq404 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq372
    | (have j0 := eq372 X0 X1
       grind)
    | exact resolve eq372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq690 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq197
       have i₂ := eq404 y x
       grind)
    | exact superpose eq404 eq197
    | (have j1 := eq404 (σ x) (σ y)
       grind)
    | (have r₁ := eq197
       have r₂ := eq404 y x
       grind)
    | (have r₁ := eq197
       have r₂ := eq404 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq197
       have r₂ := eq404 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq197 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq404
  have eq691 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq690
  have eq693 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq710 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq693 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq693
    | (have j0 := eq693 X0
       grind)
    | exact resolve eq693 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq693
  have eq714 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq710 X0
       grind)
    | exact superpose eq710 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq710 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq710 X0
       grind)
    | exact resolve eq12 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq720 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq714 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq806 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq720 X0 X1
       grind)
    | exact superpose eq720 eq11
    | (have j1 := eq720 X0 X1
       grind)
    | exact resolve eq11 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq818 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq806
    | (have j0 := eq806 X0 X0
       grind)
    | exact resolve eq806 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq861 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq818 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq862 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq861 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq931 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq862 X0
       grind)
    | exact superpose eq862 eq89
    | (have j0 := eq89 X0
       grind)
    | exact resolve eq89 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq932 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq862 X0
       grind)
    | exact superpose eq862 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq947 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq862 (σ X0)
       grind)
    | exact superpose eq862 eq15
    | exact resolve eq15 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq966 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq947 X0
       have i₂ := eq862 X0
       grind)
    | exact superpose eq862 eq947
    | exact resolve eq947 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862 eq947
  have eq16106 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq16
    | exact resolve eq16 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq16107 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq16106
       have r₂ := eq966 x
       grind)
    | exact resolve eq16106 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16106
  have eq16108 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16107
       have i₂ := eq966 x
       grind)
    | exact superpose eq966 eq16107
    | exact resolve eq16107 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16107
  have eq16452 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16108
       grind)
    | exact superpose eq16108 eq10
    | exact resolve eq10 eq16108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16108
  have eq16554 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16452
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16452
    | exact resolve eq16452 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16452
  have eq16606 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16554
       grind)
    | exact superpose eq16554 eq16
    | exact resolve eq16 eq16554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16554
  have eq16607 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq16606
       have r₂ := eq966 x
       grind)
    | exact resolve eq16606 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16606
  have eq16808 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq931 x
       have i₂ := eq16607
       grind)
    | exact superpose eq16607 eq931
    | (have j0 := eq931 x
       grind)
    | (have r₁ := eq931 x
       have r₂ := eq16607
       grind)
    | exact resolve eq931 eq16607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16809 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq932 x X0
       have i₂ := eq16607
       grind)
    | exact superpose eq16607 eq932
    | (have j0 := eq932 x X0
       grind)
    | (have r₁ := eq932 x x
       have r₂ := eq16607
       grind)
    | exact resolve eq932 eq16607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16607
  have eq16838 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq16809 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16809
  have eq16839 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq16808
  have eq16842 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq16838 X0
       have j1 := eq932 x X0
       grind)
    | (have r₁ := eq16838 X0
       have r₂ := eq932 x x
       grind)
    | exact resolve eq16838 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932 eq16838
  have eq16843 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq931 x
       grind)
    | (have r₁ := eq16839
       have r₂ := eq931 x
       grind)
    | exact resolve eq16839 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq16839
  have eq16844 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16843
       have i₂ := eq966 x
       grind)
    | exact superpose eq966 eq16843
    | exact resolve eq16843 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq16843
  have eq16854 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq16844
       grind)
    | exact superpose eq16844 eq10
    | exact resolve eq10 eq16844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16844
  have eq16961 : x = (M.op x x) := by
    first
    | (have i₁ := eq16854
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16854
    | exact resolve eq16854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16854
  have eq17188 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq16961
       grind)
    | exact superpose eq16961 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq16961
       grind)
    | exact resolve eq12 eq16961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16961
  have eq17229 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq17188 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17188
  have eq17599 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq16842 (σ X0)
       grind)
    | exact superpose eq16842 eq15
    | exact resolve eq15 eq16842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16842
  have eq17667 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq17599 X0
       have i₂ := eq17229 X0
       grind)
    | exact superpose eq17229 eq17599
    | exact resolve eq17599 eq17229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17229 eq17599
  have eq18237 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17667 y
       grind)
    | exact superpose eq17667 eq16
    | (have r₁ := eq16
       have r₂ := eq17667 y
       grind)
    | exact resolve eq16 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17667
  have eq18317 : False := by grind
  exact eq18317

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation2736 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq36 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq99 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
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
  clear eq18
  have eq100 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq99
    | (have j0 := eq99 X0 X1
       grind)
    | exact resolve eq99 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq102 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq191 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq204 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191 X0 X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq191
    | (have j0 := eq191 X0 X1 X2
       grind)
    | exact resolve eq191 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq191
  have eq1143 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) X1)))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (M.op X1 X1) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 (M.op (M.op X1 X1) (M.op (τ X1) X1)) X1
       have i₂ := eq9 (τ X1) X1
       grind)
    | exact superpose eq9 eq100
    | (have j0 := eq100 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq100 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1198 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 X1) (M.op (τ X0) X1)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1143 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1143
    | (have j0 := eq1143 X0 X1
       grind)
    | exact resolve eq1143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq4101 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (k (k (σ X1) X2) X3) = (M.op (σ X0) (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq204 X0 X1 X2
       grind)
    | exact superpose eq204 eq13
    | (have j0 := eq13 (k (k (σ X1) X2) X3) (M.op (σ X0) (k (σ X1) X2))
       have j1 := eq204 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq204 X0 X1 X2
       grind)
    | exact resolve eq13 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq53195 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq1198 X0 X1
       grind)
    | exact superpose eq1198 eq9
    | (have j1 := eq1198 X0 X1
       grind)
    | exact resolve eq9 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq53352 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53195 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq53195
    | (have j0 := eq53195 X0 X1
       grind)
    | exact resolve eq53195 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53195
  have eq53353 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53352 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53352
  have eq53560 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq53353 X0 X1
       grind)
    | exact superpose eq53353 eq11
    | (have j1 := eq53353 X0 X1
       grind)
    | exact resolve eq11 eq53353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53353
  have eq53802 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53560 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53560
    | (have j0 := eq53560 X0 X1
       grind)
    | exact resolve eq53560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53560
  have eq53962 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ X0) = (k (τ X0) (σ (M.op (M.op X1 X1) (M.op (τ (τ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq53802 (τ X0) X1
       grind)
    | exact superpose eq53802 eq30
    | (have j1 := eq53802 (τ X0) X1
       grind)
    | exact resolve eq30 eq53802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53802
  have eq54041 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (σ (M.op (M.op X1 X1) (M.op (τ (τ X0)) X1)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53962 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53962
    | (have j0 := eq53962 X0 X1
       grind)
    | exact resolve eq53962 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53962
  have eq60228 : ∀ X0 X1 : G, (τ (τ X0)) = (k (τ (τ X0)) (M.op (M.op X1 X1) (M.op (τ (τ X0)) X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (τ X0) (M.op (M.op X1 X1) (M.op (τ (τ X0)) X1))
       have i₂ := eq54041 X0 X1
       grind)
    | exact superpose eq54041 eq28
    | (have j1 := eq54041 X0 X1
       grind)
    | exact resolve eq28 eq54041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq54041
  have eq68046 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (M.op (M.op X1 X1) (M.op (τ X0) X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq60228 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60228
    | (have j0 := eq60228 (σ X0) X1
       grind)
    | exact resolve eq60228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60228
  have eq68274 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (M.op (M.op X1 X1) (M.op (τ X0) X1))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68046 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq68046
    | (have j0 := eq68046 X0 X1
       grind)
    | exact resolve eq68046 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68046
  have eq69119 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X1))) = X0 ∨ (σ (M.op (σ X0) (σ X0))) = (σ (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68274 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68274
    | (have j0 := eq68274 (σ X0) X1
       grind)
    | exact resolve eq68274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68274
  have eq69344 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ (M.op X0 X0))) ∨ (k X0 (M.op (M.op X1 X1) (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq69119 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq69119
    | (have j0 := eq69119 X0 X1
       grind)
    | exact resolve eq69119 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69119
  have eq69528 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (τ (σ (σ X0))) ∨ (k X0 (M.op (M.op X1 X1) (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ (M.op X0 X0))
       have i₂ := eq69344 X0 X1
       grind)
    | exact superpose eq69344 eq10
    | (have j1 := eq69344 X0 X1
       grind)
    | exact resolve eq10 eq69344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69344
  have eq69779 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (M.op (M.op X1 X1) (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq69528 X0 X1
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq69528
    | (have j0 := eq69528 X0 X1
       grind)
    | exact resolve eq69528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69528
  have eq70412 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ X0) = (k (τ X0) (M.op (M.op X1 X1) (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq69779 (τ X0) X1
       grind)
    | exact superpose eq69779 eq30
    | (have j1 := eq69779 (τ X0) X1
       grind)
    | exact resolve eq30 eq69779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq69779
  have eq70641 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (M.op (M.op X1 X1) (M.op (τ X0) X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70412 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70412
    | (have j0 := eq70412 X0 X1
       grind)
    | exact resolve eq70412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70412
  have eq71723 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) (M.op (τ (M.op X0 X0)) (M.op (τ X1) (τ X0)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70641 X1 (τ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq70641
    | (have j0 := eq70641 X1 X1
       grind)
    | exact resolve eq70641 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70641
  have eq83354 : ∀ X0 X1 : G, (k X0 (M.op (τ (M.op X1 X1)) (M.op X0 (τ X1)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71723 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71723
    | (have j0 := eq71723 X0 (σ X0)
       grind)
    | exact resolve eq71723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71723
  have eq83630 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (M.op (τ (M.op X1 X1)) (M.op X0 (τ X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83354 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq83354
    | (have j0 := eq83354 X0 X1
       grind)
    | exact resolve eq83354 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83354
  have eq84266 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X0 (M.op (τ (M.op X1 X1)) (M.op X0 (τ X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq83630 X0 X1
       grind)
    | exact superpose eq83630 eq10
    | (have j1 := eq83630 X0 X1
       grind)
    | exact resolve eq10 eq83630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83630
  have eq84499 : ∀ X0 X1 : G, (k X0 (M.op (τ (M.op X1 X1)) (M.op X0 (τ X1)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84266 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84266
    | (have j0 := eq84266 X0 X1
       grind)
    | exact resolve eq84266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84266
  have eq84538 : ∀ X0 X1 : G, (k X1 (M.op (τ (τ (M.op X0 X0))) (M.op X1 (τ (τ X0))))) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84499 X1 (τ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq84499
    | (have j0 := eq84499 X1 X1
       grind)
    | exact resolve eq84499 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84499
  have eq85658 : ∀ X0 X1 : G, (k X1 (M.op (τ (τ (τ (M.op X0 X0)))) (M.op X1 (τ (τ (τ X0)))))) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84538 (τ X0) X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq84538
    | (have j0 := eq84538 X0 X1
       grind)
    | exact resolve eq84538 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq84538
  have eq232100 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4101 X2 X0 X1 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4101
  have eq232101 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq232100 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232100
  have eq232106 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232101 X0 X1 X2
       have i₂ := eq36 X0 X1 X2
       grind)
    | exact superpose eq36 eq232101
    | (have j0 := eq232101 X0 X1 X2
       grind)
    | exact resolve eq232101 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq232101
  have eq232107 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq232106 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232106
  have eq232575 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (k X1 (τ X2))
       have i₂ := eq232107 X1 X2 (τ X0)
       grind)
    | exact superpose eq232107 eq19
    | (have j1 := eq232107 X1 X2 (τ X0)
       grind)
    | exact resolve eq19 eq232107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232107
  have eq232924 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232575 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq232575
    | (have j0 := eq232575 X0 X1 X2
       grind)
    | exact resolve eq232575 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232575
  have eq233062 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232924 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq232924
    | (have j0 := eq232924 X0 X1 X2
       grind)
    | exact resolve eq232924 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232924
  have eq233165 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233062 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq233062
    | (have j0 := eq233062 X0 X1 X2
       grind)
    | exact resolve eq233062 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233062
  have eq233384 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) ∨ (k X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233165 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq233165
    | exact resolve eq233165 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233165
  have eq234737 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq234744 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ X0 = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq233384 x (M.op (τ (τ (τ (M.op X0 X0)))) (M.op x (τ (τ (τ X0))))) X2
       have i₂ := eq85658 X0 x
       grind)
    | exact superpose eq85658 eq233384
    | (have j0 := eq233384 X0 X2 (M.op X2 X0)
       have j1 := eq85658 X0 X0
       grind)
    | exact resolve eq233384 eq85658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85658 eq233384
  have eq236374 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq234737 X0 X1
       have i₂ := eq234744 X0 X2
       grind)
    | exact superpose eq234744 eq234737
    | (have j1 := eq234744 X0 X1
       grind)
    | exact resolve eq234737 eq234744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234737 eq234744
  have eq293352 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq236374 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236374
  have eq293353 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq293352 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293352
  have eq293354 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq293353 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293353
  have eq293663 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq293354 X1 (τ X0)
       grind)
    | exact superpose eq293354 eq19
    | (have j1 := eq293354 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq293354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq293901 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq293354 (σ X1) (σ X0)
       grind)
    | exact superpose eq293354 eq15
    | (have j1 := eq293354 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq293354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293354
  have eq297525 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq293663 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq293663
    | exact resolve eq293663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293663
  have eq298006 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq297525 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq297525
    | (have j0 := eq297525 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq297525 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297525
  have eq302843 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq293901 x y
       grind)
    | exact superpose eq293901 eq16
    | (have j1 := eq293901 x y
       grind)
    | exact resolve eq16 eq293901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293901
  have eq303047 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq302843
       have i₂ := eq298006 x y
       grind)
    | exact superpose eq298006 eq302843
    | (have j1 := eq298006 (σ x) (σ y)
       grind)
    | (have r₁ := eq302843
       have r₂ := eq298006 x y
       grind)
    | (have r₁ := eq302843
       have r₂ := eq298006 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq302843
       have r₂ := eq298006 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq302843 eq298006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298006 eq302843
  have eq303052 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq303047
  have eq304141 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq303052
       grind)
    | exact superpose eq303052 eq16
    | exact resolve eq16 eq303052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303052
  have eq304142 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq304141
       have r₂ := eq22 x
       grind)
    | exact resolve eq304141 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304141
  have eq304143 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq304142
       grind)
    | exact superpose eq304142 eq16
    | exact resolve eq16 eq304142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304144 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq304142
       grind)
    | exact superpose eq304142 eq10
    | exact resolve eq10 eq304142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304142
  have eq304579 : x = y := by
    first
    | (have i₁ := eq304144
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq304144
    | exact resolve eq304144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304144
  have eq304580 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq304143
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq304143
    | exact resolve eq304143 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq304143
  have eq304587 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq304580
       have i₂ := eq304579
       grind)
    | exact superpose eq304579 eq304580
    | exact resolve eq304580 eq304579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304579 eq304580
  have eq304588 : False := by grind
  exact eq304588

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation2736 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  clear eq18
  have eq184 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq16
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq724 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq779 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq724 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq724
    | (have j0 := eq724 X0 X1
       grind)
    | exact resolve eq724 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq874 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 (τ X1) (τ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq189
    | (have j0 := eq189 (τ X1) (τ X0)
       grind)
    | exact resolve eq189 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq882 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq874 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq874
    | (have j0 := eq874 X0 X1
       grind)
    | exact resolve eq874 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq885 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq882 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq882
    | (have j0 := eq882 X0 X1
       grind)
    | exact resolve eq882 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq887 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq885 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq885
    | (have j0 := eq885 X0 X1
       grind)
    | exact resolve eq885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq888 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq887 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq887
    | (have j0 := eq887 X0 X1
       grind)
    | exact resolve eq887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq889 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq888
    | (have j0 := eq888 X0 X1
       grind)
    | exact resolve eq888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq890 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq889 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq889
    | (have j0 := eq889 X0 X1
       grind)
    | exact resolve eq889 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq1056 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq184
       have i₂ := eq779 y x
       grind)
    | exact superpose eq779 eq184
    | (have j1 := eq779 (σ y) (σ x)
       grind)
    | (have r₁ := eq184
       have r₂ := eq779 y x
       grind)
    | (have r₁ := eq184
       have r₂ := eq779 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq184
       have r₂ := eq779 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq184 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq779
  have eq1057 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1056
  have eq22189 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1057
       grind)
    | exact superpose eq1057 eq16
    | exact resolve eq16 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq22190 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22189
       have r₂ := eq22 x
       grind)
    | exact resolve eq22189 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22189
  have eq22195 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq22190
       grind)
    | exact superpose eq22190 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22190
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22190
       grind)
    | exact resolve eq13 eq22190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22190
  have eq22197 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22195
  have eq28408 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22197
       grind)
    | exact superpose eq22197 eq16
    | exact resolve eq16 eq22197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22197
  have eq28409 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq28408
       have r₂ := eq22 x
       grind)
    | exact resolve eq28408 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28408
  have eq28423 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq28409
       grind)
    | exact superpose eq28409 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28409
       grind)
    | exact resolve eq13 eq28409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28409
  have eq28425 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq28423
  have eq28426 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq28425
  have eq28429 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq28426
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq28426
    | exact resolve eq28426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28426
  have eq28859 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq189 x y
       have i₂ := eq28429
       grind)
    | exact superpose eq28429 eq189
    | (have j0 := eq189 x y
       grind)
    | (have r₁ := eq189 x y
       have r₂ := eq28429
       grind)
    | exact resolve eq189 eq28429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28429
  have eq28885 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq28859
  have eq28886 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq28885
  have eq28892 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq189 x y
       grind)
    | (have r₁ := eq28886
       have r₂ := eq189 x y
       grind)
    | exact resolve eq28886 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq28886
  have eq29335 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28892
       grind)
    | exact superpose eq28892 eq16
    | exact resolve eq16 eq28892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29347 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq28892
       grind)
    | exact superpose eq28892 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28892
       grind)
    | exact resolve eq13 eq28892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28892
  have eq29349 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq29347
  have eq29350 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq29349
  have eq29353 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq29350
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq29350
    | exact resolve eq29350 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29350
  have eq29931 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29353
       grind)
    | exact superpose eq29353 eq10
    | exact resolve eq10 eq29353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29353
  have eq30036 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq29931
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29931
    | exact resolve eq29931 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29931
  have eq30038 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30036
       grind)
    | exact superpose eq30036 eq16
    | exact resolve eq16 eq30036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30036
  have eq30039 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq30038
       have r₂ := eq22 x
       grind)
    | exact resolve eq30038 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30038
  have eq30494 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq30039
       grind)
    | exact superpose eq30039 eq10
    | exact resolve eq10 eq30039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30039
  have eq30601 : x = (k y x) := by
    first
    | (have i₁ := eq30494
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30494
    | exact resolve eq30494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30494
  have eq30619 : x ≠ x ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq890 y x
       have i₂ := eq30601
       grind)
    | exact superpose eq30601 eq890
    | (have j0 := eq890 y x
       grind)
    | (have r₁ := eq890 y x
       have r₂ := eq30601
       grind)
    | exact resolve eq890 eq30601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq30601
  have eq30634 : x = (M.op x y) ∨ x = y := by grind
  clear eq30619
  have eq31058 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29335
       have i₂ := eq30634
       grind)
    | exact superpose eq30634 eq29335
    | exact resolve eq29335 eq30634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29335 eq30634
  have eq31069 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq31058
  have eq31070 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31069
       grind)
    | exact superpose eq31069 eq16
    | exact resolve eq16 eq31069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31069
  have eq31075 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq31070
       have r₂ := eq22 x
       grind)
    | exact resolve eq31070 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31070
  have eq31419 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31075
       grind)
    | exact superpose eq31075 eq16
    | exact resolve eq16 eq31075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31420 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq31075
       grind)
    | exact superpose eq31075 eq10
    | exact resolve eq10 eq31075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31075
  have eq31525 : x = y := by
    first
    | (have i₁ := eq31420
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31420
    | exact resolve eq31420 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31420
  have eq31526 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq31419
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq31419
    | exact resolve eq31419 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31419
  have eq31529 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq31526
       have i₂ := eq31525
       grind)
    | exact superpose eq31525 eq31526
    | exact resolve eq31526 eq31525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31525 eq31526
  have eq31530 : False := by grind
  exact eq31530

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pyx_y_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 X2)) = (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op (M.op X1 X1) (M.op X0 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq65 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq13
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq13
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq55
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq69
  have eq72 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq60 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq60
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq77 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq74
  have eq84 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) := by
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
  have eq87 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (M.op X0 X1) X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq72
    | exact resolve eq72 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq131 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq131
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq131
    | exact resolve eq131 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq138 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq137
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq139 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq138
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq138
    | exact resolve eq138 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq149 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq151 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq154 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq77 eq149
    | exact resolve eq149 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq149
  have eq155 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq154
    | exact resolve eq154 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq407 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq666 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq90 X0 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq53
    | (have j1 := eq90 X0 X1
       grind)
    | exact resolve eq53 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq678 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq666 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq692 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq678 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq678 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq678 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq678 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq701 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq692
    | (have j0 := eq692 X0 X1
       grind)
    | exact resolve eq692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq857 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 (M.op (σ X0) X1)
       have i₂ := eq72 (σ X0) X1
       grind)
    | exact superpose eq72 eq407
    | exact resolve eq407 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq407
  have eq887 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq857 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq857
    | exact resolve eq857 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq3770 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq5716 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq152
    | (have j0 := eq152 (M.op x y)
       grind)
    | exact resolve eq152 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq5735 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5716
  have eq5740 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq151 eq5735
    | exact resolve eq5735 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq5735
  have eq5768 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5740
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5740 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740
  have eq6446 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq701 y x
       have i₂ := eq126
       grind)
    | exact superpose eq126 eq701
    | (have j0 := eq701 y x
       grind)
    | exact resolve eq701 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq701
  have eq6502 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6446
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6446
    | exact resolve eq6446 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6446
  have eq6584 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6502
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6502
    | exact resolve eq6502 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6502
  have eq6666 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6584
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6584
    | exact resolve eq6584 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6584
  have eq6742 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6666
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6666
    | exact resolve eq6666 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6666
  have eq6809 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq6742
    | exact resolve eq6742 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6742
  have eq8043 : (σ (σ (M.op x y))) ≠ (σ (σ (M.op x y))) ∨ (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ x))) ∨ (σ (σ (M.op x y))) = (M.op (σ (σ x)) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq155 eq675
    | (have j0 := eq675 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq675 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8125 : (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ x))) ∨ (σ (σ (M.op x y))) = (M.op (σ (σ x)) (σ (σ (M.op x y)))) := by grind
  clear eq8043
  have eq14557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq139 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq14557
    | exact resolve eq14557 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14557
  have eq14575 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq14564
       have r₂ := eq27
       grind)
    | exact resolve eq14564 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14564
  have eq14579 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq14575
    | exact resolve eq14575 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14575
  have eq14585 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14579 eq53
    | exact resolve eq53 eq14579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14579
  have eq14604 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14585
    | exact resolve eq14585 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14585
  have eq15036 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq113 y x
       have i₂ := eq14604
       grind)
    | exact superpose eq14604 eq113
    | exact resolve eq113 eq14604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14604
  have eq16051 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq675 x y
       have i₂ := eq15036
       grind)
    | exact superpose eq15036 eq675
    | (have j0 := eq675 x y
       grind)
    | exact resolve eq675 eq15036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15036
  have eq16055 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16051
  have eq16060 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16055
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16055
    | exact resolve eq16055 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16055
  have eq16074 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16060
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16060
    | exact resolve eq16060 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16060
  have eq16084 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16074
    | exact resolve eq16074 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16074
  have eq16085 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16084
  have eq16091 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16085
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16085
    | exact resolve eq16085 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16085
  have eq16101 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16091
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16091
    | exact resolve eq16091 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16091
  have eq16443 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16101 eq53
    | exact resolve eq53 eq16101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16101
  have eq16465 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16443
    | exact resolve eq16443 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16443
  have eq16466 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16465
  have eq16476 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16466 eq70
    | exact resolve eq70 eq16466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16466
  have eq16527 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16476 eq136
    | exact resolve eq136 eq16476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16476
  have eq16555 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq16527
    | exact resolve eq16527 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16527
  have eq17632 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq16555
       grind)
    | exact superpose eq16555 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq16555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16555
  have eq17643 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17632
  have eq17653 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17643
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17643
    | exact resolve eq17643 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17643
  have eq17654 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17653
  have eq17791 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq17654
       grind)
    | exact superpose eq17654 eq53
    | exact resolve eq53 eq17654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17654
  have eq17812 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17791
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17791
    | exact resolve eq17791 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17791
  have eq17956 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17812 eq27
    | exact resolve eq27 eq17812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17964 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17812 eq87
    | (have r₁ := eq87
       have r₂ := eq17812
       grind)
    | exact resolve eq87 eq17812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq17975 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17964
  have eq28223 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17975 eq136
    | exact resolve eq136 eq17975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq17975
  have eq28278 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq28223
    | exact resolve eq28223 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28223
  have eq28290 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28278 eq53
    | exact resolve eq53 eq28278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28278
  have eq28321 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq28290
    | exact resolve eq28290 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28290
  have eq28342 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq28321
       grind)
    | exact superpose eq28321 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq28321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28321
  have eq28369 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28342
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28342
    | exact resolve eq28342 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28342
  have eq28370 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq28369
  have eq28389 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28370
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28370
    | exact resolve eq28370 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28370
  have eq28390 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28389
  have eq28492 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq28390
       grind)
    | exact superpose eq28390 eq53
    | exact resolve eq53 eq28390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28390
  have eq28521 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28492
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28492
    | exact resolve eq28492 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28492
  have eq28522 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq28521
  have eq28532 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28522 eq70
    | exact resolve eq70 eq28522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq28549 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28522 eq17812
    | exact resolve eq17812 eq28522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17812 eq28522
  have eq28582 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq28549
  have eq28588 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28582 eq29
    | exact resolve eq29 eq28582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28582
  have eq28798 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq28588
    | exact resolve eq28588 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28588
  have eq28847 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28798 eq20
    | exact resolve eq20 eq28798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28798
  have eq28972 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq28847
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28847
    | exact resolve eq28847 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28847
  have eq29087 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28972 eq6809
    | exact resolve eq6809 eq28972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6809 eq28972
  have eq29195 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq29087
       have r₂ := eq155
       grind)
    | exact resolve eq29087 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29087
  have eq29255 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq29195
       have r₂ := eq27
       grind)
    | exact resolve eq29195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29195
  have eq29294 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq155 eq29255
    | exact resolve eq29255 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq29255
  have eq29376 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29294 eq28
    | exact resolve eq28 eq29294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq29294
  have eq29740 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq29376
    | exact resolve eq29376 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29376
  have eq29741 : x = (M.op x y) ∨ x = y := by grind
  clear eq29740
  have eq42343 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28532 eq139
    | exact resolve eq139 eq28532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq28532
  have eq42387 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq42343
  have eq42401 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq42387
       have r₂ := eq17956
       grind)
    | exact resolve eq42387 eq17956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17956 eq42387
  have eq43079 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq42401
       grind)
    | exact superpose eq42401 eq53
    | exact resolve eq53 eq42401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42401
  have eq43115 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43079
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43079
    | exact resolve eq43079 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43079
  have eq43116 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq43115
  have eq43233 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq43116
  have eq43236 : x = (M.op x y) := by
    first
    | (have r₁ := eq43233
       have r₂ := eq29741
       grind)
    | exact resolve eq43233 eq29741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29741 eq43233
  have eq43335 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq43236 eq20
    | exact resolve eq20 eq43236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq43343 : x ≠ x ∨ x = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq43236 eq84
    | (have r₁ := eq84
       have r₂ := eq43236
       grind)
    | exact resolve eq84 eq43236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq43439 : y = (k x y) ∨ x = (M.op y x) := by grind
  clear eq43343
  have eq43486 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq43335
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43335
    | exact resolve eq43335 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43335
  have eq43516 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq43486 eq26
    | exact resolve eq26 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43841 : (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) ∨ (σ (σ (M.op x y))) = (M.op (σ (σ x)) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq43486 eq8125
    | exact resolve eq8125 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8125
  have eq43842 : (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) ∨ (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq43486 eq43841
    | exact resolve eq43841 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43841
  have eq43843 : (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by grind
  clear eq43842
  have eq44022 : (σ (M.op x y)) = (k (σ (M.op x y)) (τ (σ (σ (M.op x y))))) := by
    first
    | exact superpose eq43843 eq887
    | exact resolve eq887 eq43843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq43843
  have eq44202 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq44022
       have i₂ := eq16 sF1
       grind)
    | exact superpose eq16 eq44022
    | exact resolve eq44022 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44022
  have eq44210 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5768 eq44202
    | exact resolve eq44202 eq5768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5768 eq44202
  have eq44314 : (M.op (σ (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq44210 eq3770
    | exact resolve eq3770 eq44210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770
  have eq44368 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq43486 eq44314
    | exact resolve eq44314 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44314
  have eq44416 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq44210 eq44368
    | exact resolve eq44368 eq44210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44210 eq44368
  have eq44465 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq44416 eq113
    | exact resolve eq113 eq44416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44416
  have eq53098 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq43439
       grind)
    | exact superpose eq43439 eq44
    | exact resolve eq44 eq43439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq53118 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq670 x y
       have i₂ := eq43439
       grind)
    | exact superpose eq43439 eq670
    | (have j0 := eq670 x y
       grind)
    | exact resolve eq670 eq43439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq43439
  have eq53124 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq53118
  have eq53131 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq53124
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53124
    | exact resolve eq53124 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53124
  have eq53143 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq43486 eq53098
    | exact resolve eq53098 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53098
  have eq53149 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq43486 eq53131
    | exact resolve eq53131 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53131
  have eq53161 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq53143
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq53143
    | exact resolve eq53143 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53143
  have eq53167 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq53149
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq53149
    | exact resolve eq53149 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53149
  have eq53180 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq53167
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq53167
    | exact resolve eq53167 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53167
  have eq53187 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq53180
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53180
    | exact resolve eq53180 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53180
  have eq53194 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq53187
    | exact resolve eq53187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53187
  have eq53201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq43486 eq53194
    | exact resolve eq53194 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53194
  have eq53208 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq53201
       have r₂ := eq27
       grind)
    | exact resolve eq53201 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53201
  have eq53934 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq53208 eq53
    | exact resolve eq53 eq53208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53208
  have eq53977 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43516 eq53934
    | exact resolve eq53934 eq43516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53934
  have eq53994 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq113 y x
       have i₂ := eq53977
       grind)
    | exact superpose eq53977 eq113
    | exact resolve eq113 eq53977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq53977
  have eq54556 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq675 x y
       have i₂ := eq53994
       grind)
    | exact superpose eq53994 eq675
    | (have j0 := eq675 x y
       grind)
    | exact resolve eq675 eq53994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq53994
  have eq54561 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54556
  have eq54569 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54561
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54561
    | exact resolve eq54561 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54561
  have eq54586 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54569
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54569
    | exact resolve eq54569 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54569
  have eq54603 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq54586
    | exact resolve eq54586 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq54586
  have eq54616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43486 eq54603
    | exact resolve eq54603 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54603
  have eq54623 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq54616
       have r₂ := eq27
       grind)
    | exact resolve eq54616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54616
  have eq54629 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54623
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54623
    | exact resolve eq54623 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54623
  have eq54633 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43486 eq54629
    | exact resolve eq54629 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54629
  have eq54637 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54633
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54633
    | exact resolve eq54633 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54633
  have eq58380 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54637 eq53
    | exact resolve eq53 eq54637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54637
  have eq58425 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43516 eq58380
    | exact resolve eq58380 eq43516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43516 eq58380
  have eq58426 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq58425
  have eq58434 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq58426 eq27
    | exact resolve eq27 eq58426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq58523 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq58426 eq44465
    | exact resolve eq44465 eq58426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44465 eq58426
  have eq59317 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq58523 eq53161
    | exact resolve eq53161 eq58523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53161 eq58523
  have eq59340 : x = (M.op y x) := by
    first
    | (have r₁ := eq59317
       have r₂ := eq58434
       grind)
    | exact resolve eq59317 eq58434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59317
  have eq59499 : y = (M.op x y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq59340
       grind)
    | exact superpose eq59340 eq53
    | exact resolve eq53 eq59340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq59340
  have eq59544 : y = (M.op x y) := by
    first
    | (have i₁ := eq59499
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59499
    | exact resolve eq59499 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq59499
  have eq59549 : x = y := by
    first
    | exact superpose eq43236 eq59544
    | exact resolve eq59544 eq43236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43236 eq59544
  have eq59562 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq59549
       grind)
    | exact superpose eq59549 eq24
    | exact resolve eq24 eq59549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq59549
  have eq59735 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq59562
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq59562
    | exact resolve eq59562 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq59562
  have eq59793 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq43486 eq59735
    | exact resolve eq59735 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43486 eq59735
  have eq59839 : False := by grind
  exact eq59839

/-- `Equation2744`: `x = ((y ◇ y) ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation2744 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2744 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2744.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op X1 X0)) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq106 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq108
    | exact resolve eq108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq494 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq502 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  clear eq18
  have eq511 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq494 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq494
    | (have j0 := eq494 X0 X1
       grind)
    | exact resolve eq494 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq711 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq511 x y
       grind)
    | exact superpose eq511 eq16
    | (have j1 := eq511 x y
       grind)
    | exact resolve eq16 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq3266 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq502 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq502
    | exact resolve eq502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq3324 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3266 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3266
    | (have j0 := eq3266 X0 X1
       grind)
    | exact resolve eq3266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3266
  have eq6826 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq711
       have i₂ := eq3324 y x
       grind)
    | exact superpose eq3324 eq711
    | (have j1 := eq3324 y x
       grind)
    | (have r₁ := eq711
       have r₂ := eq3324 y x
       grind)
    | (have r₁ := eq711
       have r₂ := eq3324 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq711
       have r₂ := eq3324 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq711 eq3324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq3324
  have eq6827 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6826
  have eq15043 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6827
       grind)
    | exact superpose eq6827 eq16
    | exact resolve eq16 eq6827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6827
  have eq15044 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15043
       have r₂ := eq22 x
       grind)
    | exact resolve eq15043 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15043
  have eq15047 : y = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq15044
       grind)
    | exact superpose eq15044 eq9
    | exact resolve eq9 eq15044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15044
  have eq15049 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15047
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq15047
    | exact resolve eq15047 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15047
  have eq15050 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15049
       grind)
    | exact superpose eq15049 eq16
    | exact resolve eq16 eq15049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15049
  have eq15051 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15050
       have r₂ := eq22 x
       grind)
    | exact resolve eq15050 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15050
  have eq15055 : (σ y) = (M.op (M.op (σ (M.op x x)) (σ (M.op x x))) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq106 x (σ y)
       have i₂ := eq15051
       grind)
    | exact superpose eq15051 eq106
    | exact resolve eq106 eq15051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq15051
  have eq15068 : (σ y) = (M.op (σ (M.op (M.op x x) (M.op x x))) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15055
       have i₂ := eq22 (M.op x x)
       grind)
    | exact superpose eq22 eq15055
    | exact resolve eq15055 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15055
  have eq15073 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15068
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq15068
    | exact resolve eq15068 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq15068
  have eq15074 : (σ x) = (σ y) := by grind
  clear eq15073
  have eq15079 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15074
       grind)
    | exact superpose eq15074 eq16
    | exact resolve eq16 eq15074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15080 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15074
       grind)
    | exact superpose eq15074 eq10
    | exact resolve eq10 eq15074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15074
  have eq15244 : x = y := by
    first
    | (have i₁ := eq15080
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15080
    | exact resolve eq15080 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15080
  have eq15245 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq15079
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq15079
    | exact resolve eq15079 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15079
  have eq15246 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq15245
       have i₂ := eq15244
       grind)
    | exact superpose eq15244 eq15245
    | exact resolve eq15245 eq15244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15244 eq15245
  have eq15247 : False := by grind
  exact eq15247

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X0) X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X1) (M.op (M.op X1 X1) X0)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq60 (M.op X0 X0) X1
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq130 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq37
  have eq134 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq130
  have eq135 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq134
  have eq211 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq217 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq129
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq217
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq217
    | exact resolve eq217 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq227 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq226
    | exact resolve eq226 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq255 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq135
       grind)
    | exact superpose eq135 eq16
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq345 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq211
       have i₂ := eq86 X0 sF2
       grind)
    | (have i₁ := eq211
       have i₂ := eq86 sF2 x
       grind)
    | exact superpose eq86 eq211
    | exact resolve eq211 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq211
  have eq379 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq61
    | exact resolve eq61 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq61
  have eq10817 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq227 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq10818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq10817
    | exact resolve eq10817 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10817
  have eq10829 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq10818
       have r₂ := eq28
       grind)
    | exact resolve eq10818 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10818
  have eq10834 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10829 eq60
    | exact resolve eq60 eq10829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq10829
  have eq10840 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq10834
    | exact resolve eq10834 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10834
  have eq10843 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq10840
       grind)
    | exact superpose eq10840 eq56
    | exact resolve eq56 eq10840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10840
  have eq10999 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq379 y X0
       have i₂ := eq10843
       grind)
    | exact superpose eq10843 eq379
    | exact resolve eq379 eq10843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq10843
  have eq11029 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10999 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10999
    | (have j0 := eq10999 X0
       grind)
    | exact resolve eq10999 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10999
  have eq12062 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq11029 eq27
    | (have j1 := eq11029 (σ y)
       grind)
    | exact resolve eq27 eq11029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11029
  have eq12103 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12062
  have eq12254 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12103 eq28
    | exact resolve eq28 eq12103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12256 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12103 eq67
    | exact resolve eq67 eq12103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq12103
  have eq12401 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12256 eq255
    | exact resolve eq255 eq12256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq12256
  have eq12467 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq12401
    | exact resolve eq12401 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12401
  have eq13789 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq12467
       grind)
    | exact superpose eq12467 eq56
    | exact resolve eq56 eq12467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq12467
  have eq13795 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13789
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13789
    | exact resolve eq13789 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13789
  have eq13971 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13795 eq30
    | exact resolve eq30 eq13795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13795
  have eq14102 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq13971
    | exact resolve eq13971 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13971
  have eq14103 : y = (M.op x y) ∨ x = y := by grind
  clear eq14102
  have eq14125 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14103 eq21
    | exact resolve eq21 eq14103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14235 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14125
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14125
    | exact resolve eq14125 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14125
  have eq14353 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14235 eq12254
    | (have r₁ := eq12254
       have r₂ := eq14235
       grind)
    | exact resolve eq12254 eq14235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12254 eq14235
  have eq14366 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq14353
  have eq14367 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq14366
  have eq14609 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq14367 eq29
    | exact resolve eq29 eq14367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14367
  have eq14753 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq14609
    | exact resolve eq14609 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14609
  have eq15061 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14753 eq14103
    | exact resolve eq14103 eq14753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14103 eq14753
  have eq15062 : x = y := by grind
  clear eq15061
  have eq15147 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15062
       grind)
    | exact superpose eq15062 eq19
    | exact resolve eq19 eq15062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15148 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15062
       grind)
    | exact superpose eq15062 eq25
    | exact resolve eq25 eq15062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15062
  have eq15256 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15148
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15148
    | exact resolve eq15148 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15148
  have eq15288 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15256 eq27
    | exact resolve eq27 eq15256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15256
  have eq15848 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15288 eq345
    | exact resolve eq345 eq15288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq15288
  have eq15889 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq15848
       have i₂ := eq15147
       grind)
    | exact superpose eq15147 eq15848
    | exact resolve eq15848 eq15147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15147 eq15848
  have eq16079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15889 eq15
    | exact resolve eq15 eq15889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15889
  have eq16124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16079
    | exact resolve eq16079 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16079
  have eq16138 : False := by grind
  exact eq16138

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X0) X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X1) (M.op (M.op X1 X1) X0)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq60 (M.op X0 X0) X1
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq132 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq135 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq131
  have eq136 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq135
  have eq177 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq185 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq177
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq177
    | exact resolve eq177 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq186 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq185
    | exact resolve eq185 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq187 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq186
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq186
    | exact resolve eq186 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq206 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq52
       have i₂ := eq86 X0 x
       grind)
    | (have i₁ := eq52
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq52
    | exact resolve eq52 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq225 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq132
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq132
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq65 eq225
    | exact resolve eq225 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq235 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq234
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq234
    | exact resolve eq234 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq236 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq65 eq235
    | exact resolve eq235 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq254 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq136
       grind)
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq334 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq345 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq210
       have i₂ := eq86 X0 sF2
       grind)
    | (have i₁ := eq210
       have i₂ := eq86 sF2 x
       grind)
    | exact superpose eq86 eq210
    | exact resolve eq210 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq61
    | exact resolve eq61 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq521 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq56
    | (have j1 := eq69 X0 X1
       grind)
    | exact resolve eq56 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq69
  have eq836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq187 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq837 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq836
    | exact resolve eq836 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq840 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq837
       have r₂ := eq28
       grind)
    | exact resolve eq837 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq842 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq840
    | exact resolve eq840 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq846 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq842 eq67
    | exact resolve eq67 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq848 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq842 eq28
    | exact resolve eq28 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq902 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq846
       have i₂ := eq86 X0 sF3
       grind)
    | (have i₁ := eq846
       have i₂ := eq86 sF3 x
       grind)
    | exact superpose eq86 eq846
    | exact resolve eq846 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq846 eq61
    | exact resolve eq61 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq1028 : (σ x) = (σ (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq906 eq206
    | exact resolve eq206 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq906
  have eq1043 : (σ x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1028 eq16
    | exact resolve eq16 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1057 : (σ x) = (σ y) ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1043
    | exact resolve eq1043 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1112 : y = (τ (σ x)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1057 eq30
    | exact resolve eq30 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1131 : x = y ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1112
    | exact resolve eq1112 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1132 : y = (M.op x y) ∨ x = (σ x) ∨ x = y := by grind
  clear eq1131
  have eq1138 : x = (M.op y y) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq1132 eq65
    | exact resolve eq65 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1256 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (σ x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq61 X0 y
       have i₂ := eq1138
       grind)
    | exact superpose eq1138 eq61
    | exact resolve eq61 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1463 : x = (τ x) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq345 x
       have i₂ := eq1256 x
       grind)
    | exact superpose eq1256 eq345
    | exact resolve eq345 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1534 : x = (σ x) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq1463
       grind)
    | exact superpose eq1463 eq15
    | exact resolve eq15 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq1556 : x = (σ x) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1534
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1534
    | exact resolve eq1534 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1557 : x = (σ x) ∨ x = y := by grind
  clear eq1556
  have eq1558 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | exact superpose eq1557 eq27
    | exact resolve eq27 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1560 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1557 eq36
    | exact resolve eq36 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1561 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1557 eq40
    | exact resolve eq40 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2658 : ∀ X0 : G, (k x X0) = (σ (k x (τ X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1560 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1560
    | exact resolve eq1560 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq2697 : ∀ X0 : G, (k x X0) = (k (σ x) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2658 X0
       have i₂ := eq39 X0 x
       grind)
    | exact superpose eq39 eq2658
    | exact resolve eq2658 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2658
  have eq2699 : ∀ X0 : G, (k x X0) = (k (σ x) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2697 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2697
    | (have j0 := eq2697 X0
       grind)
    | exact resolve eq2697 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697
  have eq2716 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2699 eq39
    | exact resolve eq39 eq2699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699
  have eq2734 : ∀ X0 : G, (k (σ x) X0) = (k (σ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2716 X0
       have i₂ := eq39 X0 x
       grind)
    | exact superpose eq39 eq2716
    | exact resolve eq2716 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2716
  have eq2747 : ∀ X0 : G, (k (σ x) X0) = (k (σ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2734 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2734
    | (have j0 := eq2734 X0
       grind)
    | exact resolve eq2734 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq3191 : ∀ X0 : G, (k X0 x) = (σ (k (τ X0) x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1561 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1561
    | exact resolve eq1561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq3242 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3191 X0
       have i₂ := eq35 X0 x
       grind)
    | exact superpose eq35 eq3191
    | exact resolve eq3191 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3191
  have eq3244 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3242 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3242
    | (have j0 := eq3242 X0
       grind)
    | exact resolve eq3242 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq3261 : (k (σ x) (σ x)) = (k (σ (σ x)) x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3244 eq2747
    | exact resolve eq2747 eq3244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747 eq3244
  have eq3283 : (k (σ x) (σ x)) = (k (σ (σ x)) x) ∨ x = y := by grind
  clear eq3261
  have eq3300 : (M.op (σ x) (σ x)) = (k (σ (σ x)) x) ∨ x = y := by grind
  clear eq3283
  have eq3787 : (τ (M.op (σ x) (σ x))) = (k (σ x) (τ x)) ∨ x = y := by
    first
    | exact superpose eq3300 eq334
    | exact resolve eq334 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq3300
  have eq3795 : (M.op x x) = (k (σ x) (τ x)) ∨ x = y := by
    first
    | exact superpose eq210 eq3787
    | exact resolve eq3787 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq3787
  have eq4802 : (σ (τ x)) = (M.op (σ (M.op x x)) (σ (σ x))) ∨ (σ (τ x)) = (M.op (σ (σ x)) (σ (τ x))) ∨ (σ (σ x)) = (σ (τ x)) ∨ x = y := by
    first
    | exact superpose eq3795 eq521
    | (have j0 := eq521 (σ x) (τ x)
       grind)
    | exact resolve eq521 eq3795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3795
  have eq4828 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq132 eq521
    | (have j0 := eq521 y (M.op x y)
       grind)
    | exact resolve eq521 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq521
  have eq4898 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq4828
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4828
    | exact resolve eq4828 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828
  have eq4922 : (σ (σ x)) = (σ (τ x)) ∨ (σ (τ x)) = (M.op (σ (σ x)) (σ (τ x))) ∨ (σ (σ x)) = (σ (τ x)) ∨ x = y := by
    first
    | (have i₁ := eq4802
       have i₂ := eq378 x (σ sF2)
       grind)
    | exact superpose eq378 eq4802
    | exact resolve eq4802 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq4802
  have eq4923 : (σ (σ x)) = (σ (τ x)) ∨ (σ (τ x)) = (M.op (σ (σ x)) (σ (τ x))) ∨ x = y := by grind
  clear eq4922
  have eq4957 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq4898
    | exact resolve eq4898 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4898
  have eq4978 : x = (σ (σ x)) ∨ (σ (τ x)) = (M.op (σ (σ x)) (σ (τ x))) ∨ x = y := by
    first
    | (have i₁ := eq4923
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq4923
    | exact resolve eq4923 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4923
  have eq5007 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq4957
    | exact resolve eq4957 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957
  have eq5028 : x = (M.op (σ (σ x)) x) ∨ x = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq4978
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq4978
    | exact resolve eq4978 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4978
  have eq5051 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq5007
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5007
    | exact resolve eq5007 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5007
  have eq5077 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq21 eq5051
    | exact resolve eq5051 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5051
  have eq5103 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5077
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5077
    | exact resolve eq5077 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5077
  have eq31149 : (M.op x x) = (σ (σ x)) ∨ x = (σ (σ x)) ∨ x = y := by
    first
    | exact superpose eq5028 eq60
    | exact resolve eq60 eq5028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5028
  have eq36391 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq236 eq5103
    | exact resolve eq5103 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq5103
  have eq36400 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq36391
    | exact resolve eq36391 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36391
  have eq36401 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq36400
       have r₂ := eq28
       grind)
    | exact resolve eq36400 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36400
  have eq52299 : ∀ X0 : G, (M.op X0 X0) = (σ (σ x)) ∨ x = (σ (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq31149
       have i₂ := eq86 X0 x
       grind)
    | (have i₁ := eq31149
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq31149
    | exact resolve eq31149 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq31149
  have eq71363 : (M.op y y) = (τ (σ (σ x))) ∨ x = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq254
       have i₂ := eq52299 sF3
       grind)
    | exact superpose eq52299 eq254
    | exact resolve eq254 eq52299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq71474 : (σ x) = (M.op y y) ∨ x = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq71363
       have i₂ := eq16 sF2
       grind)
    | exact superpose eq16 eq71363
    | exact resolve eq71363 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71363
  have eq71516 : (τ (σ x)) = (M.op x x) ∨ x = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq345 y
       have i₂ := eq71474
       grind)
    | exact superpose eq71474 eq345
    | exact resolve eq345 eq71474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71474
  have eq71534 : x = (M.op x x) ∨ x = (σ (σ x)) ∨ x = y := by
    first
    | exact superpose eq29 eq71516
    | exact resolve eq71516 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71516
  have eq72708 : x = (σ (σ x)) ∨ x = (σ (σ x)) ∨ x = y ∨ x = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52299 x
       have i₂ := eq71534
       grind)
    | exact superpose eq71534 eq52299
    | exact resolve eq52299 eq71534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52299 eq71534
  have eq72714 : x = (σ (σ x)) ∨ x = y := by grind
  clear eq72708
  have eq72803 : (σ x) = (τ x) ∨ x = y := by
    first
    | exact superpose eq72714 eq16
    | exact resolve eq16 eq72714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72714
  have eq213248 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36401 eq60
    | exact resolve eq60 eq36401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq36401
  have eq213293 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq213248 eq902
    | exact resolve eq902 eq213248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq213248
  have eq213305 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq213293
  have eq213310 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq213305
       have r₂ := eq848
       grind)
    | exact resolve eq213305 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq213305
  have eq214242 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq213310 eq30
    | exact resolve eq30 eq213310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq213310
  have eq214374 : x = y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq214242
    | exact resolve eq214242 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq214242
  have eq214375 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq214374
  have eq214383 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq214375 eq21
    | exact resolve eq21 eq214375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214386 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq214375 eq65
    | exact resolve eq65 eq214375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq214375
  have eq214715 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq214383
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq214383
    | exact resolve eq214383 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214383
  have eq215851 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y
       have i₂ := eq214386
       grind)
    | exact superpose eq214386 eq61
    | exact resolve eq61 eq214386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq214386
  have eq219290 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1558
       have i₂ := eq215851 sF3
       grind)
    | exact superpose eq215851 eq1558
    | exact resolve eq1558 eq215851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215851
  have eq219357 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq219290
  have eq219413 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq219357 eq28
    | exact resolve eq28 eq219357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219357
  have eq219424 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq219413
       have r₂ := eq214715
       grind)
    | exact resolve eq219413 eq214715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214715 eq219413
  have eq219427 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq219424 eq21
    | exact resolve eq21 eq219424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219429 : y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq219424 eq57
    | exact resolve eq57 eq219424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq219424
  have eq219755 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq219427
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq219427
    | exact resolve eq219427 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219427
  have eq220755 : x = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq219755 eq1557
    | exact resolve eq1557 eq219755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq221419 : x = (σ (M.op x y)) ∨ x = y := by grind
  clear eq220755
  have eq221472 : (M.op x y) = (τ x) ∨ x = y := by
    first
    | exact superpose eq221419 eq31
    | exact resolve eq31 eq221419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq221419
  have eq222572 : (M.op x y) = (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq72803
       have i₂ := eq221472
       grind)
    | exact superpose eq221472 eq72803
    | exact resolve eq72803 eq221472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72803 eq221472
  have eq222968 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq222572
  have eq223426 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq222968 eq219755
    | exact resolve eq219755 eq222968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219755 eq222968
  have eq223427 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by grind
  clear eq223426
  have eq228589 : y = (τ y) ∨ x = y := by
    first
    | (have i₁ := eq345 x
       have i₂ := eq219429
       grind)
    | exact superpose eq219429 eq345
    | exact resolve eq345 eq219429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219429
  have eq229585 : y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq228589
       grind)
    | exact superpose eq228589 eq15
    | exact resolve eq15 eq228589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228589
  have eq229906 : y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq229585
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq229585
    | exact resolve eq229585 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229585
  have eq229947 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq229906 eq1558
    | exact resolve eq1558 eq229906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558 eq229906
  have eq230022 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq229947
  have eq230036 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq230022
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq230022
    | exact resolve eq230022 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230022
  have eq230040 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq230036 eq28
    | exact resolve eq28 eq230036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230036
  have eq230057 : x = y := by
    first
    | (have r₁ := eq230040
       have r₂ := eq223427
       grind)
    | exact resolve eq230040 eq223427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223427 eq230040
  have eq231001 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq230057
       grind)
    | exact superpose eq230057 eq19
    | exact resolve eq19 eq230057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq231002 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq230057
       grind)
    | exact superpose eq230057 eq25
    | exact resolve eq25 eq230057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq230057
  have eq231304 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq231002
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq231002
    | exact resolve eq231002 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq231002
  have eq231336 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq231304 eq27
    | exact resolve eq27 eq231304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq231304
  have eq233390 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq231336 eq345
    | exact resolve eq345 eq231336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq231336
  have eq233419 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq233390
       have i₂ := eq231001
       grind)
    | exact superpose eq231001 eq233390
    | exact resolve eq233390 eq231001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231001 eq233390
  have eq233791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq233419 eq15
    | exact resolve eq15 eq233419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233419
  have eq234322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq233791
    | exact resolve eq233791 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq233791
  have eq234457 : False := by grind
  exact eq234457
