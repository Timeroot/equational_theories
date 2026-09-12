import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq83 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq15
    | exact resolve eq15 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq92
    | exact resolve eq92 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq92
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq119
    | exact resolve eq119 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq120
  have eq601 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq603 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq606 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq601 X0 X1
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq601
    | (have j0 := eq601 X0 X1
       grind)
    | exact resolve eq601 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq879 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq606 x y
       grind)
    | exact superpose eq606 eq16
    | (have j1 := eq606 x y
       grind)
    | exact resolve eq16 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq34913 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq603
    | exact resolve eq603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq35034 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34913 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34913
    | (have j0 := eq34913 X0 X1
       grind)
    | exact resolve eq34913 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34913
  have eq68257 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq879
       have i₂ := eq35034 y x
       grind)
    | exact superpose eq35034 eq879
    | (have j1 := eq35034 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq879
       have r₂ := eq35034 y x
       grind)
    | (have r₁ := eq879
       have r₂ := eq35034 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq879
       have r₂ := eq35034 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq879 eq35034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq35034
  have eq68258 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq68257
  have eq68260 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68258
       grind)
    | exact superpose eq68258 eq16
    | exact resolve eq16 eq68258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68258
  have eq68261 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq68260
       have r₂ := eq99 x
       grind)
    | exact resolve eq68260 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68260
  have eq68263 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq68261
       grind)
    | exact superpose eq68261 eq10
    | exact resolve eq10 eq68261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68261
  have eq68325 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68263
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq68263
    | exact resolve eq68263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68263
  have eq68328 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68325
       grind)
    | exact superpose eq68325 eq16
    | exact resolve eq16 eq68325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68325
  have eq68329 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq68328
       have r₂ := eq99 x
       grind)
    | exact resolve eq68328 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq68328
  have eq68348 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq68329
       grind)
    | exact superpose eq68329 eq10
    | exact resolve eq10 eq68329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68329
  have eq68414 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68348
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq68348
    | exact resolve eq68348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68348
  have eq68415 : y = (M.op x x) := by grind
  clear eq68414
  have eq68425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123 x
       have i₂ := eq68415
       grind)
    | exact superpose eq68415 eq123
    | exact resolve eq123 eq68415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq68415
  have eq68534 : False := by grind
  exact eq68534

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq271 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq271 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq271
    | (have j0 := eq271 (σ X0) (σ X1)
       grind)
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq271 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq271
    | (have j0 := eq271 (τ X0) (τ X1)
       grind)
    | exact resolve eq271 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq287 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq271 (σ X0) X1
       grind)
    | exact superpose eq271 eq28
    | (have j1 := eq271 (σ X0) X1
       grind)
    | exact resolve eq28 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 X2 X3 : G, (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (M.op X2 X1) X3))) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq287 X0 (M.op (M.op X3 X1) X0)
       have i₂ := eq63 X0 X1 (σ X0) X3
       grind)
    | exact superpose eq63 eq287
    | (have j0 := eq287 X0 X1
       grind)
    | exact resolve eq287 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 X2 X3 : G, (k X0 (τ X1)) = (k X0 (τ (M.op (M.op X2 X1) X3))) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq287 eq373
    | (have j0 := eq373 X0 X1 X2 X3
       have j1 := eq287 X0 X1
       grind)
    | exact resolve eq373 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq373
  have eq408 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq271 X0 X1
       grind)
    | exact superpose eq271 eq272
    | (have j0 := eq272 X0 X1
       have j1 := eq271 (σ X0) (σ X1)
       grind)
    | exact resolve eq272 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq273 X0 X0
       grind)
    | exact superpose eq273 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq273 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X1)
       have r₂ := eq273 X1 X1
       grind)
    | exact resolve eq12 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq549 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq544 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq544 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq544 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq627 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq549 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq549
    | (have j0 := eq549 (σ X0) X1
       grind)
    | exact resolve eq549 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq627
    | (have j0 := eq627 X0 X1
       grind)
    | exact resolve eq627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq631 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq628
    | (have j0 := eq628 X0 X1
       grind)
    | exact resolve eq628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq636 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq631 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq631
    | (have j0 := eq631 (σ X0) X1
       grind)
    | exact resolve eq631 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1973 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq408 x y
       grind)
    | exact superpose eq408 eq16
    | (have j1 := eq408 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq408 x y
       grind)
    | exact resolve eq16 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq1981 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1973
  have eq1992 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1981
       grind)
    | exact superpose eq1981 eq16
    | exact resolve eq16 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1994 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ y) X0 (σ x)
       have i₂ := eq1981
       grind)
    | exact superpose eq1981 eq63
    | exact resolve eq63 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1999 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1994 X0 (σ y)
       have i₂ := eq1981
       grind)
    | exact superpose eq1981 eq1994
    | exact resolve eq1994 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq2010 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1999 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2023 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1981
       have i₂ := eq2010 (σ x)
       grind)
    | exact superpose eq2010 eq1981
    | exact resolve eq1981 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2029 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2023
  have eq2039 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq2029
       grind)
    | exact superpose eq2029 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq2029
       grind)
    | exact resolve eq12 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2041 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq2042 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2041 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq2041
    | exact resolve eq2041 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2058 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq549 (σ x) X0
       have i₂ := eq2041 (σ x)
       grind)
    | exact superpose eq2041 eq549
    | (have j0 := eq549 (σ x) X0
       grind)
    | exact resolve eq549 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq2041
  have eq2102 : ∀ X0 : G, x ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2058 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2058
    | (have j0 := eq2058 X0
       grind)
    | exact resolve eq2058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq2105 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2102 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2102
    | exact resolve eq2102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq2106 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x ≠ (τ (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2029 eq2105
    | (have j0 := eq2105 X0
       grind)
    | exact resolve eq2105 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105
  have eq2107 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2106 X0
       grind)
    | (have r₁ := eq2106 X0
       have r₂ := eq10 x
       grind)
    | exact resolve eq2106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106
  have eq2140 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2107 eq2042
    | exact resolve eq2042 eq2107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042 eq2107
  have eq2155 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2029
       have i₂ := eq2140 x
       grind)
    | exact superpose eq2140 eq2029
    | exact resolve eq2029 eq2140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029 eq2140
  have eq2162 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq2155
  have eq2169 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2162
       grind)
    | exact superpose eq2162 eq10
    | exact resolve eq10 eq2162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq2264 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2169
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2169
    | exact resolve eq2169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169
  have eq2290 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 x
       have i₂ := eq2264
       grind)
    | exact superpose eq2264 eq63
    | exact resolve eq63 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2293 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2290 X0 y
       have i₂ := eq2264
       grind)
    | exact superpose eq2264 eq2290
    | exact resolve eq2290 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2304 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq2293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2293
  have eq2310 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2304 x
       have i₂ := eq2264
       grind)
    | exact superpose eq2264 eq2304
    | exact resolve eq2304 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264 eq2304
  have eq2321 : x = (M.op x x) := by grind
  clear eq2310
  have eq2327 : x = (M.op x x) := by grind
  clear eq2321
  have eq2331 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq2327
       grind)
    | exact superpose eq2327 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq2327
       grind)
    | exact resolve eq12 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2332 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 x X0 x
       have i₂ := eq2327
       grind)
    | exact superpose eq2327 eq63
    | exact resolve eq63 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2333 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq2331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331
  have eq2334 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq636 x X0
       have i₂ := eq2333 x
       grind)
    | exact superpose eq2333 eq636
    | (have j0 := eq636 x X0
       grind)
    | exact resolve eq636 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2360 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2334 X0
       have i₂ := eq2327
       grind)
    | exact superpose eq2327 eq2334
    | (have j0 := eq2334 X0
       grind)
    | exact resolve eq2334 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2361 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq2360 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2447 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq22 X0 x
       have i₂ := eq2361 X0
       grind)
    | exact superpose eq2361 eq22
    | exact resolve eq22 eq2361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2463 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2361 (σ X0)
       grind)
    | exact superpose eq2361 eq15
    | exact resolve eq15 eq2361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361
  have eq2511 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq2463 X0
       have i₂ := eq2333 X0
       grind)
    | exact superpose eq2333 eq2463
    | exact resolve eq2463 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463
  have eq2522 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq2447 X0
       have i₂ := eq2333 (τ X0)
       grind)
    | exact superpose eq2333 eq2447
    | exact resolve eq2447 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447
  have eq2745 : ∀ X0 X1 X2 : G, (M.op X1 (σ x)) = (M.op X1 (M.op (σ (M.op X0 x)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X2 (σ x) X1 (σ X0)
       have i₂ := eq2511 X0
       grind)
    | exact superpose eq2511 eq63
    | exact resolve eq63 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2952 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X1 (σ (M.op (M.op X0 x) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq2745 X0 X1 (σ x)
       have i₂ := eq2511 (M.op X0 x)
       grind)
    | exact superpose eq2511 eq2745
    | exact resolve eq2745 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22726 : ∀ X0 X1 X2 : G, (k X2 (τ X1)) = (k X2 (M.op (τ (M.op X0 X1)) x)) ∨ (σ X2) = (M.op (σ X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq404 X2 X1 X0 (σ x)
       have i₂ := eq2522 (M.op X0 X1)
       grind)
    | exact superpose eq2522 eq404
    | (have j0 := eq404 X2 X1 X2 x
       grind)
    | exact resolve eq404 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq71361 : ∀ X0 : G, (k X0 (τ (σ y))) = (k X0 (M.op (τ (σ x)) x)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22726 (σ x) (σ y) X0
       have i₂ := eq1981
       grind)
    | exact superpose eq1981 eq22726
    | (have j0 := eq22726 X0 (σ y) X0
       grind)
    | exact resolve eq22726 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981 eq22726
  have eq71608 : ∀ X0 : G, (k X0 (τ (σ y))) = (k X0 (M.op x x)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq71361 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq71361
    | (have j0 := eq71361 X0
       grind)
    | exact resolve eq71361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71361
  have eq71745 : ∀ X0 : G, (k X0 (τ (σ y))) = (k X0 x) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq71608 X0
       have i₂ := eq2327
       grind)
    | exact superpose eq2327 eq71608
    | (have j0 := eq71608 X0
       grind)
    | exact resolve eq71608 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71608
  have eq71869 : ∀ X0 : G, (k X0 (τ (σ y))) = (M.op X0 x) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq71745 X0
       have i₂ := eq2333 X0
       grind)
    | exact superpose eq2333 eq71745
    | (have j0 := eq71745 X0
       grind)
    | exact resolve eq71745 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333 eq71745
  have eq71968 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ y)) ∨ (k X0 y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq71869 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq71869
    | (have j0 := eq71869 X0
       grind)
    | exact resolve eq71869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71869
  have eq81630 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op y x) = (k y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq71968 y
       grind)
    | exact superpose eq71968 eq12
    | (have j0 := eq12 X0 (σ y)
       have j1 := eq71968 y
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq71968 y
       grind)
    | exact resolve eq12 eq71968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71968
  have eq81644 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op y x) = (k y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq81630 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81630
  have eq81657 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ y)) ∨ (M.op y x) = (k y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2010 eq81644
    | exact resolve eq81644 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81644
  have eq130883 : ∀ X0 : G, (τ (M.op (σ X0) (σ x))) = (k X0 (τ (σ y))) ∨ (M.op y x) = (k y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ y)
       have i₂ := eq81657 (σ X0)
       grind)
    | exact superpose eq81657 eq28
    | exact resolve eq28 eq81657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81657
  have eq131070 : ∀ X0 : G, (k X0 y) = (τ (M.op (σ X0) (σ x))) ∨ (M.op y x) = (k y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq130883 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq130883
    | exact resolve eq130883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130883
  have eq131186 : ∀ X0 : G, (k X0 y) = (M.op (τ (σ X0)) x) ∨ (M.op y x) = (k y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq131070 X0
       have i₂ := eq2522 (σ X0)
       grind)
    | exact superpose eq2522 eq131070
    | exact resolve eq131070 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131070
  have eq131258 : ∀ X0 : G, (k X0 y) = (M.op X0 x) ∨ (M.op y x) = (k y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq131186 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq131186
    | exact resolve eq131186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131186
  have eq131420 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq131258 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131258
  have eq131421 : (M.op y x) = (k y y) ∨ x = (M.op x y) := by grind
  clear eq131420
  have eq132697 : (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq131421
       have i₂ := eq271 y y
       grind)
    | exact superpose eq271 eq131421
    | (have j1 := eq271 x y
       grind)
    | exact resolve eq131421 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq137270 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 y
       have i₂ := eq132697
       grind)
    | exact superpose eq132697 eq63
    | exact resolve eq63 eq132697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132697
  have eq137292 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq137270 X0 x
       have i₂ := eq63 x x X0 y
       grind)
    | exact superpose eq63 eq137270
    | exact resolve eq137270 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137270
  have eq137377 : x ≠ (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq137292
  have eq137380 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq137377
       have r₂ := eq2327
       grind)
    | exact resolve eq137377 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137377
  have eq137427 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq137380
       grind)
    | exact superpose eq137380 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq137380
       grind)
    | exact resolve eq12 eq137380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137442 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq137427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137427
  have eq137564 : (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131421
       have i₂ := eq137442 y
       grind)
    | exact superpose eq137442 eq131421
    | exact resolve eq131421 eq137442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137442
  have eq137565 : (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq137564
  have eq137571 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq137380 eq137565
    | exact resolve eq137565 eq137380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137380 eq137565
  have eq137596 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq137571 eq131421
    | exact resolve eq131421 eq137571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131421
  have eq137715 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq636 y X0
       have i₂ := eq137596
       grind)
    | exact superpose eq137596 eq636
    | (have j0 := eq636 y X0
       grind)
    | exact resolve eq636 eq137596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq137596
  have eq137743 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq137715 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137715
  have eq137753 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2010 eq137743
    | exact resolve eq137743 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010 eq137743
  have eq138263 : ∀ X0 : G, (τ (M.op (σ X0) (σ x))) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ y)
       have i₂ := eq137753 (σ X0)
       grind)
    | exact superpose eq137753 eq28
    | exact resolve eq28 eq137753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq137753
  have eq138472 : ∀ X0 : G, (k X0 y) = (τ (M.op (σ X0) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq138263 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq138263
    | exact resolve eq138263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138263
  have eq138628 : ∀ X0 : G, (k X0 y) = (M.op (τ (σ X0)) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq138472 X0
       have i₂ := eq2522 (σ X0)
       grind)
    | exact superpose eq2522 eq138472
    | exact resolve eq138472 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522 eq138472
  have eq138741 : ∀ X0 : G, (k X0 y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq138628 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138628
    | exact resolve eq138628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138628
  have eq138838 : ∀ X0 : G, y ≠ (M.op y x) ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq631 y X0
       have i₂ := eq138741 y
       grind)
    | exact superpose eq138741 eq631
    | (have j0 := eq631 y X0
       grind)
    | exact resolve eq631 eq138741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq139048 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq138838 X0
       grind)
    | (have r₁ := eq138838 X0
       have r₂ := eq137571
       grind)
    | exact resolve eq138838 eq137571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137571 eq138838
  have eq139094 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq138741 eq139048
    | exact resolve eq139048 eq138741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138741 eq139048
  have eq139103 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq139094 eq1992
    | exact resolve eq1992 eq139094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992 eq139094
  have eq139206 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139103
       have i₂ := eq2327
       grind)
    | exact superpose eq2327 eq139103
    | exact resolve eq139103 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139103
  have eq139207 : x = (M.op x y) := by grind
  clear eq139206
  have eq139233 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq139207
       grind)
    | exact superpose eq139207 eq16
    | exact resolve eq16 eq139207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139238 : x ≠ x ∨ y = (M.op y y) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq139207
       grind)
    | exact superpose eq139207 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq139207
       grind)
    | exact resolve eq13 eq139207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139239 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 x
       have i₂ := eq139207
       grind)
    | exact superpose eq139207 eq63
    | exact resolve eq63 eq139207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139207
  have eq139253 : y = (M.op y y) ∨ (k x y) = (M.op y x) := by grind
  clear eq139238
  have eq139254 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq139239 X0 x
       have i₂ := eq2332 X0 x
       grind)
    | exact superpose eq2332 eq139239
    | exact resolve eq139239 eq2332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2332 eq139239
  have eq139367 : (k x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq139253
       have i₂ := eq139254 y
       grind)
    | exact superpose eq139254 eq139253
    | exact resolve eq139253 eq139254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139253 eq139254
  have eq139371 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq272 x y
       have i₂ := eq139367
       grind)
    | exact superpose eq139367 eq272
    | (have j0 := eq272 x y
       grind)
    | exact resolve eq272 eq139367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq139367
  have eq139387 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq139371
       have r₂ := eq139233
       grind)
    | exact resolve eq139371 eq139233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139371
  have eq141536 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ y) X0 (σ x)
       have i₂ := eq139387
       grind)
    | exact superpose eq139387 eq63
    | exact resolve eq63 eq139387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq139387
  have eq141560 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq141536 X0 x
       have i₂ := eq2745 y X0 x
       grind)
    | exact superpose eq2745 eq141536
    | exact resolve eq141536 eq2745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2745 eq141536
  have eq141683 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq139233
       have i₂ := eq141560 (σ x)
       grind)
    | exact superpose eq141560 eq139233
    | exact resolve eq139233 eq141560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141560
  have eq141740 : (σ x) ≠ (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq141683
       have i₂ := eq2511 x
       grind)
    | exact superpose eq2511 eq141683
    | exact resolve eq141683 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141683
  have eq141788 : (σ x) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq141740
       have i₂ := eq2327
       grind)
    | exact superpose eq2327 eq141740
    | exact resolve eq141740 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141740
  have eq141789 : y = (M.op y x) := by grind
  clear eq141788
  have eq141902 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq2952 y X0
       have i₂ := eq141789
       grind)
    | exact superpose eq141789 eq2952
    | exact resolve eq2952 eq141789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952
  have eq142005 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq141902 X0
       have i₂ := eq141789
       grind)
    | exact superpose eq141789 eq141902
    | exact resolve eq141902 eq141789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141789 eq141902
  have eq142583 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq142005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142005
  have eq143396 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq139233
       have i₂ := eq142583 (σ x)
       grind)
    | exact superpose eq142583 eq139233
    | exact resolve eq139233 eq142583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139233 eq142583
  have eq143546 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq143396
       have i₂ := eq2511 x
       grind)
    | exact superpose eq2511 eq143396
    | exact resolve eq143396 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511 eq143396
  have eq143592 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq143546
       have i₂ := eq2327
       grind)
    | exact superpose eq2327 eq143546
    | exact resolve eq143546 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327 eq143546
  have eq143593 : False := by grind
  exact eq143593

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq269 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq269 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq269
    | (have j0 := eq269 (σ X0) (σ X1)
       grind)
    | exact resolve eq269 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq269 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq269
    | (have j0 := eq269 (τ X0) (τ X1)
       grind)
    | exact resolve eq269 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq404 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq270 X1 X0
       have i₂ := eq269 X1 X0
       grind)
    | exact superpose eq269 eq270
    | (have j0 := eq270 X1 X0
       have j1 := eq269 (σ X1) (σ X0)
       grind)
    | exact resolve eq270 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq540 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq271 X0 X0
       grind)
    | exact superpose eq271 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq271 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq271 X0 X0
       grind)
    | exact resolve eq12 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X1 X0)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq545 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq540 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq540 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq540 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq552 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq543 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq543
    | (have j0 := eq543 (σ X1) (σ X0)
       grind)
    | exact resolve eq543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq562 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq552
    | (have j0 := eq552 X0 X1
       grind)
    | exact resolve eq552 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq564 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq562
    | (have j0 := eq562 X0 X1
       grind)
    | exact resolve eq562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq565 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq564
    | (have j0 := eq564 X0 X1
       grind)
    | exact resolve eq564 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq566 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq565
    | (have j0 := eq565 X0 X1
       grind)
    | exact resolve eq565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq568 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq566 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq566
    | (have j0 := eq566 (σ X0) (σ X1)
       grind)
    | exact resolve eq566 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq623 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq545 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq545
    | (have j0 := eq545 (σ X0) X1
       grind)
    | exact resolve eq545 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq624 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq623 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq623
    | (have j0 := eq623 X0 X1
       grind)
    | exact resolve eq623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq627 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq624
    | (have j0 := eq624 X0 X1
       grind)
    | exact resolve eq624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq632 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq627 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq627
    | (have j0 := eq627 (σ X0) X1
       grind)
    | exact resolve eq627 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq5070 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq404 x y
       grind)
    | exact superpose eq404 eq16
    | (have j1 := eq404 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq404 x y
       grind)
    | exact resolve eq16 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq5082 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5070
  have eq5103 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5082
       grind)
    | exact superpose eq5082 eq16
    | exact resolve eq16 eq5082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5104 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq5082
       grind)
    | exact superpose eq5082 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq5082
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5082
       grind)
    | exact resolve eq13 eq5082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5082
  have eq5106 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq5104
  have eq5108 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5106
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5106
    | exact resolve eq5106 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106
  have eq5110 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq269 eq5108
    | (have j1 := eq269 (σ x) (σ x)
       grind)
    | exact resolve eq5108 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq5108
  have eq5111 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5110
       have r₂ := eq5103
       grind)
    | exact resolve eq5110 eq5103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5103 eq5110
  have eq5113 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq5111
       grind)
    | exact superpose eq5111 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq5111
       grind)
    | exact resolve eq12 eq5111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5115 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5113
  have eq5117 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5115 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq5115
    | exact resolve eq5115 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5146 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq545 (σ x) X0
       have i₂ := eq5115 (σ x)
       grind)
    | exact superpose eq5115 eq545
    | (have j0 := eq545 (σ x) X0
       grind)
    | exact resolve eq545 eq5115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq5115
  have eq5227 : ∀ X0 : G, x ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5146 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5146
    | (have j0 := eq5146 X0
       grind)
    | exact resolve eq5146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5146
  have eq5237 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5227 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5227
    | exact resolve eq5227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5227
  have eq5239 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x ≠ (τ (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5111 eq5237
    | (have j0 := eq5237 X0
       grind)
    | exact resolve eq5237 eq5111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111 eq5237
  have eq5241 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5239 X0
       grind)
    | (have r₁ := eq5239 X0
       have r₂ := eq10 x
       grind)
    | exact resolve eq5239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5239
  have eq5384 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5241 eq5117
    | exact resolve eq5117 eq5241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5117 eq5241
  have eq5401 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5384 y
       grind)
    | exact superpose eq5384 eq16
    | (have r₁ := eq16
       have r₂ := eq5384 y
       grind)
    | exact resolve eq16 eq5384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5384
  have eq5414 : y = (M.op x y) := by grind
  clear eq5401
  have eq5447 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5414
       grind)
    | exact superpose eq5414 eq16
    | exact resolve eq16 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5448 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq5414
       grind)
    | exact superpose eq5414 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5414
       grind)
    | exact resolve eq13 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5450 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq5448
  have eq5591 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq568 y x
       have i₂ := eq5450
       grind)
    | exact superpose eq5450 eq568
    | (have j0 := eq568 y x
       grind)
    | exact resolve eq568 eq5450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq5450
  have eq5594 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq5591
  have eq5601 : x = (M.op x x) := by
    first
    | (have r₁ := eq5594
       have r₂ := eq5447
       grind)
    | exact resolve eq5594 eq5447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5594
  have eq5605 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq5601
       grind)
    | exact superpose eq5601 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq5601
       grind)
    | exact resolve eq12 eq5601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5606 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 x X0 x
       have i₂ := eq5601
       grind)
    | exact superpose eq5601 eq63
    | exact resolve eq63 eq5601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq5607 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq5605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5605
  have eq5610 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq632 x X0
       have i₂ := eq5607 x
       grind)
    | exact superpose eq5607 eq632
    | (have j0 := eq632 x X0
       grind)
    | exact resolve eq632 eq5607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq5653 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq5610 X0
       have i₂ := eq5601
       grind)
    | exact superpose eq5601 eq5610
    | (have j0 := eq5610 X0
       grind)
    | exact resolve eq5610 eq5601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5610
  have eq5654 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq5653 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5653
  have eq5659 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq5606 X0 y
       have i₂ := eq5414
       grind)
    | exact superpose eq5414 eq5606
    | exact resolve eq5606 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5606
  have eq5678 : y = (M.op x x) := by
    first
    | (have i₁ := eq5414
       have i₂ := eq5659 x
       grind)
    | exact superpose eq5659 eq5414
    | exact resolve eq5414 eq5659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414 eq5659
  have eq5692 : x = y := by
    first
    | (have i₁ := eq5678
       have i₂ := eq5601
       grind)
    | exact superpose eq5601 eq5678
    | exact resolve eq5678 eq5601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5678
  have eq5693 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5447
       have i₂ := eq5692
       grind)
    | exact superpose eq5692 eq5447
    | exact resolve eq5447 eq5692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447 eq5692
  have eq5825 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq5654 (σ X0)
       grind)
    | exact superpose eq5654 eq15
    | exact resolve eq15 eq5654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5654
  have eq5909 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq5825 X0
       have i₂ := eq5607 X0
       grind)
    | exact superpose eq5607 eq5825
    | exact resolve eq5825 eq5607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5607 eq5825
  have eq6286 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5693
       have i₂ := eq5909 x
       grind)
    | exact superpose eq5909 eq5693
    | exact resolve eq5693 eq5909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5693 eq5909
  have eq6322 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6286
       have i₂ := eq5601
       grind)
    | exact superpose eq5601 eq6286
    | exact resolve eq6286 eq5601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5601 eq6286
  have eq6323 : False := by grind
  exact eq6323

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq280 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
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
  have eq283 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq283 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq285 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq280 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq286 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq284 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq284 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq284 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq299 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq286 (σ X0)
       grind)
    | exact superpose eq286 eq15
    | exact resolve eq15 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq299 X0
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq299
    | exact resolve eq299 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq299
  have eq362 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X2 (σ X0) X1 (σ X0)
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq63
    | exact resolve eq63 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq362 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq318 (M.op X0 X0)
       grind)
    | exact superpose eq318 eq362
    | exact resolve eq362 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq784 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq285 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq785 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq784 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq796 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq785 X1 (σ X0)
       grind)
    | exact superpose eq785 eq22
    | (have j1 := eq785 X1 (σ X0)
       grind)
    | exact resolve eq22 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq797 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq785 X1 (τ X0)
       grind)
    | exact superpose eq785 eq18
    | (have j1 := eq785 X1 (τ X0)
       grind)
    | exact resolve eq18 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq800 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq785 (σ X1) (σ X0)
       grind)
    | exact superpose eq785 eq15
    | (have j1 := eq785 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq785 (σ X1) X0
       grind)
    | exact superpose eq785 eq28
    | (have j1 := eq785 (σ X1) X0
       grind)
    | exact resolve eq28 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq808 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq785 (τ X1) X0
       grind)
    | exact superpose eq785 eq17
    | (have j1 := eq785 (τ X1) X0
       grind)
    | exact resolve eq17 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq785
  have eq836 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq805 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq805
    | exact resolve eq805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (M.op (M.op X1 X1) (M.op X1 X1)) (τ X0)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq805 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq390 X0 X1
       grind)
    | exact superpose eq390 eq805
    | (have j0 := eq805 X0 X1
       grind)
    | exact resolve eq805 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq805
  have eq855 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq836 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq836
    | (have j0 := eq836 X0 X1
       grind)
    | exact resolve eq836 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq860 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq855 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq855
    | (have j0 := eq855 (σ X0) (σ X1)
       grind)
    | exact resolve eq855 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq894 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq860 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq860
    | (have j0 := eq860 X0 X1
       grind)
    | exact resolve eq860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq895 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq808 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq808
    | exact resolve eq808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq942 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq895 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq895
    | (have j0 := eq895 X0 X1
       grind)
    | exact resolve eq895 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq1048 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (σ X0) X1) ∨ (τ (M.op (σ X0) X1)) = (k (τ (M.op (M.op X2 X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq796 X0 (M.op (M.op X3 X1) X0)
       have i₂ := eq63 X0 X1 (σ X0) X3
       grind)
    | exact superpose eq63 eq796
    | (have j0 := eq796 X0 X1
       grind)
    | exact resolve eq796 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq1101 : ∀ X0 X1 X2 X3 : G, (τ X0) = (M.op (τ X0) X1) ∨ (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op X2 X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq797 X0 (M.op (M.op X3 X1) X0)
       have i₂ := eq63 X0 X1 (τ X0) X3
       grind)
    | exact superpose eq63 eq797
    | (have j0 := eq797 X0 X1
       grind)
    | exact resolve eq797 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq1621 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq800 x y
       grind)
    | exact superpose eq800 eq16
    | (have j1 := eq800 x y
       grind)
    | exact resolve eq16 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1650 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq800 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1812 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1621
       have i₂ := eq942 y x
       grind)
    | exact superpose eq942 eq1621
    | (have j1 := eq942 (σ y) (σ x)
       grind)
    | (have r₁ := eq1621
       have r₂ := eq942 y x
       grind)
    | exact resolve eq1621 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq1621
  have eq1813 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1812
  have eq18127 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = X0 ∨ (τ (M.op X0 X1)) = (k (τ (M.op (M.op X2 X1) X3)) (τ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1048 (τ X0) X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1048
    | exact resolve eq1048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq18336 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = X0 ∨ (τ (M.op X0 X1)) = (τ (k (M.op (M.op X2 X1) X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18127 X0 X1 X2 X3
       have i₂ := eq31 X0 (M.op (M.op X2 X1) X3)
       grind)
    | exact superpose eq31 eq18127
    | (have j0 := eq18127 X0 X1 X2 X3
       grind)
    | exact resolve eq18127 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq18127
  have eq18468 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (τ (M.op X0 X1)) = (τ (k (M.op (M.op X2 X1) X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq18336 X0 X1 X2 X3
       grind)
    | exact superpose eq18336 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq18336 X0 X0 X2 X3
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq18336 X0 X1 X2 X3
       grind)
    | exact resolve eq13 eq18336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18336
  have eq18561 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 X1)) = (τ (k (M.op (M.op X2 X1) X3) X0)) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq18468 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18468
  have eq20088 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = X0 ∨ (σ (M.op X0 X1)) = (k (σ (M.op (M.op X2 X1) X3)) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1101 (σ X0) X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1101
    | exact resolve eq1101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq20292 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X1)) = (σ (k (M.op (M.op X2 X1) X3) X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20088 X0 X1 X2 X3
       have i₂ := eq15 (M.op (M.op X2 X1) X3) X0
       grind)
    | exact superpose eq15 eq20088
    | (have j0 := eq20088 X0 X1 X2 X3
       grind)
    | exact resolve eq20088 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20088
  have eq20520 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X2 X1) X3) X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (k (M.op (M.op X2 X1) X3) X0)
       have i₂ := eq20292 X0 X1 X2 X3
       grind)
    | exact superpose eq20292 eq10
    | (have j1 := eq20292 X0 X1 X2 X3
       grind)
    | exact resolve eq10 eq20292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20292
  have eq20582 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op (M.op X2 X1) X3) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20520 X0 X1 X2 X3
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq20520
    | (have j0 := eq20520 X0 X1 X2 X3
       grind)
    | exact resolve eq20520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20520
  have eq20681 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X1 (σ X0)) = (k (M.op (σ (M.op X0 X0)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20582 X1 (σ X0) (σ X0) X2
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq20582
    | (have j0 := eq20582 X1 (σ X0) X2 x
       grind)
    | exact resolve eq20582 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20935 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (k (M.op (σ (M.op X0 X0)) X2) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20681 X1 (σ X0) X2
       have i₂ := eq800 X0 X1
       grind)
    | exact superpose eq800 eq20681
    | (have j0 := eq20681 X0 (σ X1) X2
       have j1 := eq800 X1 X0
       grind)
    | exact resolve eq20681 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800 eq20681
  have eq21043 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (k (M.op (σ (M.op X0 X0)) X2) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq20935 X0 X1 X2
       have j1 := eq1650 X1 X0
       grind)
    | (have r₁ := eq20935 X1 X0 X2
       have r₂ := eq1650 X0 X1
       grind)
    | exact resolve eq20935 eq1650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20935
  have eq98815 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20582 (τ X0) X1 X1 (M.op X1 X1)
       have i₂ := eq839 X0 X1
       grind)
    | exact superpose eq839 eq20582
    | (have j0 := eq20582 (τ X0) X1 x x
       have j1 := eq839 X0 X1
       grind)
    | exact resolve eq20582 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq20582
  have eq199383 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21043 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq318 (M.op X0 X0)
       grind)
    | exact superpose eq318 eq21043
    | (have j0 := eq21043 X0 X1 x
       grind)
    | exact resolve eq21043 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21043
  have eq199879 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq199383 X0 X1
       have i₂ := eq15 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       grind)
    | exact superpose eq15 eq199383
    | (have j0 := eq199383 X0 X1
       grind)
    | exact resolve eq199383 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199383
  have eq470282 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X2 X1) X3) X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (k (M.op (M.op X2 X1) X3) X0)
       have i₂ := eq18561 X0 X1 X2 X3
       grind)
    | exact superpose eq18561 eq11
    | (have j1 := eq18561 X0 X1 X2 X3
       grind)
    | exact resolve eq11 eq18561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18561
  have eq470583 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op (M.op X2 X1) X3) X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq470282 X0 X1 X2 X3
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq470282
    | (have j0 := eq470282 X0 X1 X2 X3
       grind)
    | exact resolve eq470282 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470282
  have eq519428 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98815 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq98815
    | (have j0 := eq98815 X1 (τ X0)
       grind)
    | exact resolve eq98815 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98815
  have eq564338 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq519428 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519428
  have eq567443 : ∀ X0 X1 : G, (k X0 X1) ≠ (τ (σ X1)) ∨ (k X0 X1) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq564338 (σ X1) (σ X0)
       have i₂ := eq894 X0 X1
       grind)
    | exact superpose eq894 eq564338
    | (have j0 := eq564338 (σ X1) (σ X0)
       have j1 := eq894 X0 X1
       grind)
    | exact resolve eq564338 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq564338
  have eq567449 : ∀ X0 X1 : G, (k X0 X1) ≠ (τ (σ X1)) ∨ (k X0 X1) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq567443 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567443
  have eq567466 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq567449 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq567449
    | (have j0 := eq567449 X0 X1
       grind)
    | exact resolve eq567449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567449
  have eq567528 : ∀ X0 X1 : G, (k X0 X1) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq567466 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq567466
    | (have j0 := eq567466 X0 X1
       grind)
    | exact resolve eq567466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567466
  have eq567559 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq567528 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq567528
    | (have j0 := eq567528 X0 X1
       grind)
    | exact resolve eq567528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567528
  have eq601610 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (M.op (M.op X0 X0) (M.op X0 X0)) X1)
       have i₂ := eq199879 X0 X1
       grind)
    | exact superpose eq199879 eq10
    | (have j1 := eq199879 X0 X1
       grind)
    | exact resolve eq10 eq199879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199879
  have eq601879 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq601610 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq601610
    | (have j0 := eq601610 X0 X1
       grind)
    | exact resolve eq601610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601610
  have eq603103 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq470583 X1 X0 X0 (M.op X0 X0)
       have i₂ := eq601879 X0 X1
       grind)
    | exact superpose eq601879 eq470583
    | (have j0 := eq470583 X1 X0 x x
       have j1 := eq601879 X0 X1
       grind)
    | exact resolve eq470583 eq601879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470583 eq601879
  have eq603736 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq603103 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq603103 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq603103 X1 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq603103 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603103
  have eq604142 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq603736 X0 X1
       have j1 := eq567559 X0 X1
       grind)
    | (have r₁ := eq603736 X0 X1
       have r₂ := eq567559 X0 X1
       grind)
    | exact resolve eq603736 eq567559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567559 eq603736
  have eq607672 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq604142 y x
       grind)
    | exact superpose eq604142 eq16
    | (have j1 := eq604142 y x
       grind)
    | exact resolve eq16 eq604142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604142
  have eq608331 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq607672
       have i₂ := eq1813
       grind)
    | exact superpose eq1813 eq607672
    | exact resolve eq607672 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813 eq607672
  have eq608368 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq608331
  have eq608400 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1650 x y
       have i₂ := eq608368
       grind)
    | exact superpose eq608368 eq1650
    | (have j0 := eq1650 x y
       grind)
    | exact resolve eq1650 eq608368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650 eq608368
  have eq608568 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq608400
  have eq608569 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq608568
  have eq608622 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ y) X0 (σ x)
       have i₂ := eq608569
       grind)
    | exact superpose eq608569 eq63
    | exact resolve eq63 eq608569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq610055 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq608622 X0 (σ y)
       have i₂ := eq608569
       grind)
    | exact superpose eq608569 eq608622
    | exact resolve eq608622 eq608569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608622
  have eq612539 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq608569
       have i₂ := eq610055 (σ x)
       grind)
    | exact superpose eq610055 eq608569
    | exact resolve eq608569 eq610055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608569 eq610055
  have eq612740 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq612539
       have i₂ := eq318 x
       grind)
    | exact superpose eq318 eq612539
    | exact resolve eq612539 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq612539
  have eq613767 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq365 x X0
       have i₂ := eq612740
       grind)
    | exact superpose eq612740 eq365
    | (have j0 := eq365 x X0
       grind)
    | (have r₁ := eq365 x x
       have r₂ := eq612740
       grind)
    | exact resolve eq365 eq612740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq613818 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq612740
       grind)
    | exact superpose eq612740 eq10
    | exact resolve eq10 eq612740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612740
  have eq614074 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq613767 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613767
  have eq614112 : x = (M.op x x) := by
    first
    | (have i₁ := eq613818
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq613818
    | exact resolve eq613818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613818
  have eq614164 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq614112
       grind)
    | exact superpose eq614112 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq614112
       grind)
    | exact resolve eq12 eq614112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614112
  have eq614501 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq614164 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614164
  have eq616576 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq614074 (σ X0)
       grind)
    | exact superpose eq614074 eq15
    | exact resolve eq15 eq614074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614074
  have eq617024 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq616576 X0
       have i₂ := eq614501 X0
       grind)
    | exact superpose eq614501 eq616576
    | exact resolve eq616576 eq614501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614501 eq616576
  have eq628458 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq617024 y
       grind)
    | exact superpose eq617024 eq16
    | (have r₁ := eq16
       have r₂ := eq617024 y
       grind)
    | exact resolve eq16 eq617024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617024
  have eq628996 : False := by grind
  exact eq628996

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq18
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq35
  have eq94 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) (M.op (τ X0) (τ X0))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 X1 X2 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = X2 ∨ (k (σ X2) X0) = (σ (M.op (τ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq94 X0 X2
       grind)
    | exact superpose eq94 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq94 X0 X2
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq94 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact resolve eq12 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq784 : ∀ X0 X1 X2 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = X2 ∨ (k (σ X2) X0) = (σ (M.op (τ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq777 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq797 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq74 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq74 X0
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq803 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq797 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq1986 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq803 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq803
    | exact resolve eq803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq2047 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1986 X0 X1
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq1986
    | (have j0 := eq1986 X0 X1
       grind)
    | exact resolve eq1986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1986
  have eq2052 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2047 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2047
    | (have j0 := eq2047 X0 X0
       grind)
    | exact resolve eq2047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq2241 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2052 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2242 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2241 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241
  have eq2325 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2242 (σ X0)
       grind)
    | exact superpose eq2242 eq15
    | exact resolve eq15 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2362 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2325 X0
       have i₂ := eq2242 X0
       grind)
    | exact superpose eq2242 eq2325
    | exact resolve eq2325 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242 eq2325
  have eq13452 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X2 ∨ (k (σ X2) (σ X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq784 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq784
    | exact resolve eq784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq13557 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (σ (M.op X0 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13452 X0 X1 X2
       have i₂ := eq15 X2 X0
       grind)
    | exact superpose eq15 eq13452
    | (have j0 := eq13452 X0 X1 X2
       grind)
    | exact resolve eq13452 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13452
  have eq13618 : ∀ X0 X1 X2 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq13557 X0 X2 X1
       grind)
    | exact superpose eq13557 eq10
    | (have j1 := eq13557 X0 X2 X1
       grind)
    | exact resolve eq10 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13557
  have eq13688 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13618 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq13618
    | (have j0 := eq13618 X0 X1 X1
       grind)
    | exact resolve eq13618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13618
  have eq13830 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13688 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13688
  have eq13831 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13830 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13830
  have eq14054 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq13831 X1 (τ X0)
       grind)
    | exact superpose eq13831 eq19
    | (have j1 := eq13831 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq13831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14082 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq13831 (σ X1) (σ X0)
       grind)
    | exact superpose eq13831 eq15
    | (have j1 := eq13831 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq13831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13831
  have eq14648 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14054 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14054
    | exact resolve eq14054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14054
  have eq14767 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14648 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq14648
    | (have j0 := eq14648 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq14648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14648
  have eq15464 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14082 x y
       grind)
    | exact superpose eq14082 eq16
    | (have j1 := eq14082 x y
       grind)
    | exact resolve eq16 eq14082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14082
  have eq15757 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15464
       have i₂ := eq14767 x y
       grind)
    | exact superpose eq14767 eq15464
    | (have j1 := eq14767 (σ x) (σ y)
       grind)
    | (have r₁ := eq15464
       have r₂ := eq14767 x y
       grind)
    | (have r₁ := eq15464
       have r₂ := eq14767 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq15464
       have r₂ := eq14767 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq15464 eq14767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14767 eq15464
  have eq15762 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq15757
  have eq15766 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15762
       grind)
    | exact superpose eq15762 eq16
    | exact resolve eq16 eq15762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15762
  have eq15767 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq15766
       have r₂ := eq2362 x
       grind)
    | exact resolve eq15766 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15766
  have eq16003 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15767
       grind)
    | exact superpose eq15767 eq16
    | exact resolve eq16 eq15767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16004 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15767
       grind)
    | exact superpose eq15767 eq10
    | exact resolve eq10 eq15767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15767
  have eq16078 : x = y := by
    first
    | (have i₁ := eq16004
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16004
    | exact resolve eq16004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16004
  have eq16079 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16003
       have i₂ := eq2362 x
       grind)
    | exact superpose eq2362 eq16003
    | exact resolve eq16003 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362 eq16003
  have eq16088 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16079
       have i₂ := eq16078
       grind)
    | exact superpose eq16078 eq16079
    | exact resolve eq16079 eq16078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16078 eq16079
  have eq16089 : False := by grind
  exact eq16089

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq42 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
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
  clear eq30
  have eq97 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq99 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq100 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
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
  clear eq70 eq99
  have eq102 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq106 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq102
    | (have j0 := eq102 X0 X1
       grind)
    | exact resolve eq102 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq138 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X2 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq44
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq138
    | exact resolve eq138 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq290 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106 x y
       grind)
    | exact superpose eq106 eq16
    | (have j1 := eq106 x y
       grind)
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq1540 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | (have j0 := eq100 X1 (σ X0)
       grind)
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1578 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1540 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1540
    | (have j0 := eq1540 X0 X1
       grind)
    | exact resolve eq1540 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq1581 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1578 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1578
    | (have j0 := eq1578 X0 X1
       grind)
    | exact resolve eq1578 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1582 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1581 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1581
    | (have j0 := eq1581 X0 X1
       grind)
    | exact resolve eq1581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq2070 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq290
       have i₂ := eq1582 y x
       grind)
    | exact superpose eq1582 eq290
    | (have j1 := eq1582 x y
       grind)
    | (have r₁ := eq290
       have r₂ := eq1582 y x
       grind)
    | (have r₁ := eq290
       have r₂ := eq1582 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq290
       have r₂ := eq1582 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq290 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq1582
  have eq2071 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq2070
  have eq49026 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2071
       grind)
    | exact superpose eq2071 eq16
    | exact resolve eq16 eq2071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071
  have eq49027 : (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq49026
       have r₂ := eq22 x
       grind)
    | exact resolve eq49026 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49026
  have eq49556 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq49027
       grind)
    | exact superpose eq49027 eq22
    | exact resolve eq22 eq49027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49027
  have eq49648 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq49556
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq49556
    | exact resolve eq49556 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49556
  have eq49649 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq49648
  have eq49678 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq49649
       grind)
    | exact superpose eq49649 eq10
    | exact resolve eq10 eq49649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49649
  have eq49778 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq49678
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq49678
    | exact resolve eq49678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49678
  have eq49779 : (M.op x x) = (M.op y y) := by grind
  clear eq49778
  have eq50188 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq171 y x
       have i₂ := eq49779
       grind)
    | exact superpose eq49779 eq171
    | exact resolve eq171 eq49779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50245 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 y X0 y
       have i₂ := eq49779
       grind)
    | exact superpose eq49779 eq44
    | exact resolve eq44 eq49779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49779
  have eq50266 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq50245 X0 x
       have i₂ := eq44 x x X0 x
       grind)
    | exact superpose eq44 eq50245
    | exact resolve eq50245 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq50245
  have eq50299 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq50188 X0
       have i₂ := eq171 x X0
       grind)
    | exact superpose eq171 eq50188
    | exact resolve eq50188 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq50188
  have eq52063 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50299 (σ x)
       grind)
    | exact superpose eq50299 eq16
    | exact resolve eq16 eq50299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50299
  have eq52117 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq52063
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq52063
    | exact resolve eq52063 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq52063
  have eq52256 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq52117
       have i₂ := eq50266 x
       grind)
    | exact superpose eq50266 eq52117
    | exact resolve eq52117 eq50266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50266 eq52117
  have eq52257 : False := by grind
  exact eq52257

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pxy_pyx_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq70
    | (have j0 := eq70 X0
       grind)
    | exact resolve eq70 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq159 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq149 y x
       grind)
    | exact superpose eq149 eq16
    | (have j1 := eq149 y x
       grind)
    | exact resolve eq16 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq605 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq159
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq159
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq159
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq159
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq159 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq606 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq605
  have eq3996 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq606
       grind)
    | exact superpose eq606 eq16
    | exact resolve eq16 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq3997 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq3996
       have r₂ := eq23 x
       grind)
    | exact resolve eq3996 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3996
  have eq4003 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq69 y X0
       have i₂ := eq3997
       grind)
    | exact superpose eq3997 eq69
    | exact resolve eq69 eq3997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4016 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq3997
       grind)
    | exact superpose eq3997 eq9
    | exact resolve eq9 eq3997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3997
  have eq15687 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq4016 X0
       grind)
    | exact superpose eq4016 eq10
    | (have j1 := eq4016 X0
       grind)
    | exact resolve eq10 eq4016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016
  have eq15782 : ∀ X0 : G, x = y ∨ (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq15687 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15687
    | (have j0 := eq15687 X0
       grind)
    | exact resolve eq15687 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15687
  have eq15960 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq15782 X0
       grind)
    | exact superpose eq15782 eq16
    | (have j1 := eq15782 X0
       grind)
    | exact resolve eq16 eq15782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15782
  have eq15961 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq15960 X0
       grind)
    | (have r₁ := eq15960 X0
       have r₂ := eq23 x
       grind)
    | exact resolve eq15960 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15960
  have eq15988 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x X0)) = (M.op X1 (M.op (M.op X0 y) X2)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 (M.op x X0) X1 X0
       have i₂ := eq15961 X0
       grind)
    | exact superpose eq15961 eq27
    | exact resolve eq27 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961
  have eq16032 : ∀ X0 X1 : G, (σ x) = (σ (M.op y y)) ∨ (M.op X1 y) = (M.op X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15988 X0 X1 x
       have i₂ := eq27 x y X1 X0
       grind)
    | exact superpose eq27 eq15988
    | exact resolve eq15988 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15988
  have eq16046 : ∀ X0 X1 : G, (M.op y y) = (τ (σ x)) ∨ (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq16032 X1 X0
       grind)
    | exact superpose eq16032 eq10
    | (have j1 := eq16032 X1 X0
       grind)
    | exact resolve eq10 eq16032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16032
  have eq16141 : ∀ X0 X1 : G, x = (M.op y y) ∨ (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16046 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16046
    | (have j0 := eq16046 X0 X1
       grind)
    | exact resolve eq16046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16046
  have eq16438 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ (M.op X1 y) = (M.op X1 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq16141 X1 X2
       grind)
    | exact superpose eq16141 eq9
    | (have j1 := eq16141 X0 X0
       grind)
    | exact resolve eq9 eq16141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16141
  have eq16832 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq16438 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16438
  have eq16833 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq16832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16832
  have eq16865 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x X0)) = (M.op X1 (M.op (M.op X0 y) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 (M.op x X0) X1 X0
       have i₂ := eq16833 X0
       grind)
    | exact superpose eq16833 eq27
    | exact resolve eq27 eq16833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16910 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16865 X0 X1 x
       have i₂ := eq27 x y X1 X0
       grind)
    | exact superpose eq27 eq16865
    | exact resolve eq16865 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16865
  have eq260870 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq4003 X0
       grind)
    | exact superpose eq4003 eq10
    | (have j1 := eq4003 X0
       grind)
    | exact resolve eq10 eq4003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4003
  have eq261202 : ∀ X0 : G, x = y ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq260870 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq260870
    | (have j0 := eq260870 X0
       grind)
    | exact resolve eq260870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260870
  have eq262687 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq261202 X0
       grind)
    | exact superpose eq261202 eq16
    | (have j1 := eq261202 X0
       grind)
    | exact resolve eq16 eq261202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261202
  have eq262778 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq262687 X0
       grind)
    | (have r₁ := eq262687 X0
       have r₂ := eq23 x
       grind)
    | exact resolve eq262687 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262687
  have eq263933 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X2)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 (M.op (σ x) X0) X1 X0
       have i₂ := eq262778 X0
       grind)
    | exact superpose eq262778 eq27
    | exact resolve eq27 eq262778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262778
  have eq264117 : ∀ X0 X1 : G, (σ x) = (σ (M.op y y)) ∨ (M.op X1 (σ y)) = (M.op X1 (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq263933 X0 X1 x
       have i₂ := eq27 x (σ y) X1 X0
       grind)
    | exact superpose eq27 eq263933
    | exact resolve eq263933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263933
  have eq264165 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ (M.op X1 (σ y)) = (M.op X1 (M.op (σ x) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 y X0
       have i₂ := eq264117 X2 X1
       grind)
    | exact superpose eq264117 eq69
    | (have j1 := eq264117 X0 X0
       grind)
    | exact resolve eq69 eq264117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq264117
  have eq276105 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq264165 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264165
  have eq276106 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq276105 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276105
  have eq278102 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 (M.op (σ x) X0) X1 X0
       have i₂ := eq276106 X0
       grind)
    | exact superpose eq276106 eq27
    | exact resolve eq27 eq276106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276106
  have eq278289 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq278102 X0 X1 x
       have i₂ := eq27 x (σ y) X1 X0
       grind)
    | exact superpose eq27 eq278102
    | exact resolve eq278102 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq278102
  have eq279768 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq278289 (σ x) X0
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq278289
    | exact resolve eq278289 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278289
  have eq283509 : (M.op (σ x) (σ y)) = (σ (k x (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq279768 (σ x)
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq279768
    | (have j1 := eq71 x
       grind)
    | exact resolve eq279768 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq283761 : (M.op (σ (M.op x x)) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq23 (M.op x x)
       have i₂ := eq279768 (σ (M.op x x))
       grind)
    | exact superpose eq279768 eq23
    | exact resolve eq23 eq279768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq279768
  have eq284058 : (σ (M.op (M.op x x) y)) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq283761
       have i₂ := eq16910 x (M.op x x)
       grind)
    | exact superpose eq16910 eq283761
    | exact resolve eq283761 eq16910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16910 eq283761
  have eq288593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k x (M.op x x)) = (M.op x (M.op x x)) := by grind
  have eq288710 : (k x (M.op x x)) = (M.op x (M.op x x)) := by
    first
    | (have r₁ := eq288593
       have r₂ := eq16
       grind)
    | exact resolve eq288593 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288593
  have eq288745 : (M.op x y) = (k x (M.op x x)) := by
    first
    | (have i₁ := eq288710
       have i₂ := eq16833 x
       grind)
    | exact superpose eq16833 eq288710
    | exact resolve eq288710 eq16833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16833 eq288710
  have eq316648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq283509
       have i₂ := eq288745
       grind)
    | exact superpose eq288745 eq283509
    | exact resolve eq283509 eq288745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283509 eq288745
  have eq316649 : (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq316648
       have r₂ := eq16
       grind)
    | exact resolve eq316648 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316648
  have eq316680 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq316649
       grind)
    | exact superpose eq316649 eq10
    | exact resolve eq10 eq316649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316649
  have eq317139 : x = (M.op x x) := by
    first
    | (have i₁ := eq316680
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq316680
    | exact resolve eq316680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316680
  have eq317289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq284058
       have i₂ := eq317139
       grind)
    | exact superpose eq317139 eq284058
    | exact resolve eq284058 eq317139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284058 eq317139
  have eq317488 : False := by grind
  exact eq317488

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq21 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq22 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq22 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq43
    | exact resolve eq43 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq52 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq57 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq22 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq22 eq52
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq67 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq57
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq269 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq16
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X0) (σ X1) x
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq22
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq22 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq280 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq414 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq280 (M.op X0 X1)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq280
    | (have j0 := eq280 (M.op X0 X1)
       grind)
    | exact resolve eq280 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq280 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq280
    | (have j0 := eq280 (τ X0)
       grind)
    | exact resolve eq280 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq419 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq414 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq421 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq418 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq418
    | (have j0 := eq418 X0
       grind)
    | exact resolve eq418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq424 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq421 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq421
    | (have j0 := eq421 X0
       grind)
    | exact resolve eq421 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq438 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq424 (τ X0)
       have i₂ := eq67 X0 X0
       grind)
    | exact superpose eq67 eq424
    | (have j0 := eq424 (τ X0)
       grind)
    | exact resolve eq424 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq452 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq419 X0 X1
       grind)
    | exact superpose eq419 eq22
    | exact resolve eq22 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k X2 (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (τ X2)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (τ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 X2 (M.op X0 X1)
       have i₂ := eq22 X0 X1 (τ X2)
       grind)
    | exact superpose eq22 eq94
    | (have j0 := eq94 X2 (M.op X0 X1)
       grind)
    | exact resolve eq94 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq94 X0 (τ X0)
       grind)
    | exact superpose eq94 eq60
    | (have j1 := eq94 X0 (τ X0)
       grind)
    | exact resolve eq60 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq596 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op (τ X0) X1) X2
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq57
    | (have j1 := eq94 X0 X1
       grind)
    | exact resolve eq57 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq94
  have eq599 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq580 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq600 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq596 X0 X1 X2
       have i₂ := eq78 X0 X1 X2
       grind)
    | exact superpose eq78 eq596
    | (have j0 := eq596 X0 X1 X2
       grind)
    | exact resolve eq596 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq596
  have eq605 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq599 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq599
    | (have j0 := eq599 X0
       grind)
    | exact resolve eq599 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq608 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (τ X2)) ∨ (σ (M.op X0 X1)) = (k X2 (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (τ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq577 X0 X1 X2
       have i₂ := eq22 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq577
    | (have j0 := eq577 X0 X1 X2
       grind)
    | exact resolve eq577 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq859 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op (τ X1) X0)) X1) ∨ (τ X1) = (M.op (τ X1) (M.op (τ X1) X0)) ∨ (M.op (τ X1) X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (M.op (τ X1) X0) X1
       have i₂ := eq26 (τ X1) X0
       grind)
    | exact superpose eq26 eq90
    | (have j0 := eq90 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq90 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq900 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op (τ X1) X0)) X1) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (M.op (τ X1) X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq859 X0 X1
       have i₂ := eq22 (τ X1) X0 (τ X1)
       grind)
    | exact superpose eq22 eq859
    | (have j0 := eq859 X0 X1
       grind)
    | exact resolve eq859 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq956 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq438 (M.op X0 X1)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq438
    | (have j0 := eq438 (M.op X0 X1)
       grind)
    | exact resolve eq438 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq965 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq956 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq982 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq269
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq269
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq269 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983 : y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq982
  have eq1001 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
       have i₂ := eq965 X0 X1
       grind)
    | exact superpose eq965 eq22
    | exact resolve eq22 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1120 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X2 (σ (k X0 X1))) = (M.op X3 (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (σ (k X0 X1)) X3
       have i₂ := eq274 X0 X1 (M.op (σ (k X0 X1)) X2)
       grind)
    | exact superpose eq274 eq9
    | (have j1 := eq274 X0 X1 X2
       grind)
    | exact resolve eq9 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq1641 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 (k (σ X0) (σ X0)) X0
       have i₂ := eq605 (σ X0)
       grind)
    | exact superpose eq605 eq50
    | (have j1 := eq605 (σ X0)
       grind)
    | exact resolve eq50 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq1649 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1641 x
       have i₂ := eq50 (σ x) x
       grind)
    | exact superpose eq50 eq1641
    | (have j0 := eq1641 X0
       grind)
    | exact resolve eq1641 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq1665 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1649 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1649
    | (have j0 := eq1649 X0
       grind)
    | exact resolve eq1649 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq1679 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1665 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1665
    | (have j0 := eq1665 X0
       grind)
    | exact resolve eq1665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq10804 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44 y x
       have i₂ := eq983
       grind)
    | exact superpose eq983 eq44
    | exact resolve eq44 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq983
  have eq12285 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1679 (τ X0)
       have i₂ := eq600 X0 (τ X0) X0
       grind)
    | exact superpose eq600 eq1679
    | (have j0 := eq1679 (τ X0)
       have j1 := eq600 X0 (τ X0) x
       grind)
    | exact resolve eq1679 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq1679
  have eq12311 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq12285 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12285
  have eq12342 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12311 X0
       have i₂ := eq67 X0 X0
       grind)
    | exact superpose eq67 eq12311
    | (have j0 := eq12311 X0
       grind)
    | exact resolve eq12311 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12311
  have eq12370 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq12342
  have eq12388 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12370 X0
       have i₂ := eq22 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq22 eq12370
    | (have j0 := eq12370 X0
       grind)
    | exact resolve eq12370 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12370
  have eq12430 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq12388
  have eq12464 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12430 X0
       have i₂ := eq67 X0 X0
       grind)
    | exact superpose eq67 eq12430
    | (have j0 := eq12430 X0
       grind)
    | exact resolve eq12430 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12430
  have eq12465 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12464 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12464
  have eq12476 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12465 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12465
    | exact resolve eq12465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12547 : ∀ X0 X1 : G, (τ (k X0 X0)) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ X0) (τ X0) x
       have i₂ := eq12465 X0
       grind)
    | exact superpose eq12465 eq22
    | exact resolve eq22 eq12465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12548 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 (τ X0) (τ X0)
       have i₂ := eq12465 X0
       grind)
    | exact superpose eq12465 eq26
    | exact resolve eq26 eq12465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12627 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq12476 X0
       have i₂ := eq50 (σ X0) X0
       grind)
    | exact superpose eq50 eq12476
    | exact resolve eq12476 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12476
  have eq12643 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12627 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12627
    | exact resolve eq12627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12627
  have eq12774 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq12643 X0
       grind)
    | exact superpose eq12643 eq280
    | (have j0 := eq280 X0
       grind)
    | exact resolve eq280 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq12855 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq12643 (σ X0)
       grind)
    | exact superpose eq12643 eq15
    | exact resolve eq15 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12920 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12855 X0
       have i₂ := eq12643 X0
       grind)
    | exact superpose eq12643 eq12855
    | exact resolve eq12855 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12855
  have eq13757 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq12920 X0
       grind)
    | exact superpose eq12920 eq26
    | exact resolve eq26 eq12920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq14550 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) X0) ∨ (σ (M.op X1 X2)) = (k (σ X0) (σ (M.op X1 X2))) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq608 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq608
    | (have j0 := eq608 X1 X2 (σ X0)
       grind)
    | exact resolve eq608 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq14723 : ∀ X0 X1 X2 : G, (σ (M.op X1 X2)) = (σ (k X0 (M.op X1 X2))) ∨ (M.op X1 X2) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14550 X0 X1 X2
       have i₂ := eq15 X0 (M.op X1 X2)
       grind)
    | exact superpose eq15 eq14550
    | (have j0 := eq14550 X0 X1 X2
       grind)
    | exact resolve eq14550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14550
  have eq15901 : ∀ X0 : G, (τ (k X0 X0)) ≠ (τ (k X0 X0)) ∨ (τ X0) = (k (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ (k X0 X0)) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13 (τ X0) (τ (k X0 X0))
       have i₂ := eq12548 X0
       grind)
    | exact superpose eq12548 eq13
    | (have j0 := eq13 (τ X0) (τ (k X0 X0))
       grind)
    | (have r₁ := eq13 (τ X0) (τ (k X0 X0))
       have r₂ := eq12548 X0
       grind)
    | exact resolve eq13 eq12548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12548
  have eq15924 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ (k X0 X0)) (τ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq15901 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15901
  have eq15939 : ∀ X0 : G, (τ X0) = (τ (k X0 (k X0 X0))) ∨ (τ X0) = (M.op (τ (k X0 X0)) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq15924 X0
       have i₂ := eq67 (k X0 X0) X0
       grind)
    | exact superpose eq67 eq15924
    | (have j0 := eq15924 X0
       grind)
    | exact resolve eq15924 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15924
  have eq15982 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (τ X0) = (M.op (τ (k X0 X0)) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq15939 X0
       have i₂ := eq12643 X0
       grind)
    | exact superpose eq12643 eq15939
    | (have j0 := eq15939 X0
       grind)
    | exact resolve eq15939 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15939
  have eq16007 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq15982 X0
       have i₂ := eq12547 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq12547 eq15982
    | (have j0 := eq15982 X0
       grind)
    | exact resolve eq15982 eq12547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12547 eq15982
  have eq16018 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16007 X0
       have i₂ := eq12643 X0
       grind)
    | exact superpose eq12643 eq16007
    | (have j0 := eq16007 X0
       grind)
    | exact resolve eq16007 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16007
  have eq23313 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 (M.op X0 X0))) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X0 X0) X1
       have i₂ := eq16018 X0
       grind)
    | exact superpose eq16018 eq67
    | (have j1 := eq16018 X0
       grind)
    | exact resolve eq67 eq16018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23401 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (τ (k X1 X0)) = (τ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23313 X0 X1
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq23313
    | (have j0 := eq23313 X0 X1
       grind)
    | exact resolve eq23313 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq23313
  have eq27852 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (σ (k y x))) = (M.op X1 (σ (k y x))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1120 y x X0 X1
       grind)
    | exact superpose eq1120 eq16
    | (have j1 := eq1120 y x X0 X1
       grind)
    | exact resolve eq16 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq27970 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op X0 (σ (k y x))) = (M.op X1 (σ (k y x))) := by
    intro X0 X1
    first
    | (have i₁ := eq27852 X0 X1
       have i₂ := eq12920 x
       grind)
    | exact superpose eq12920 eq27852
    | (have j0 := eq27852 X0 X1
       grind)
    | exact resolve eq27852 eq12920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27852
  have eq29762 : ∀ X0 X1 : G, (k (τ (σ (M.op (τ (σ X1)) X0))) X1) = (τ (σ (M.op X0 (τ (σ X1))))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (M.op (τ (σ X1)) X0) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ (M.op (τ (σ X1)) X0)) X1
       have i₂ := eq900 X0 (σ X1)
       grind)
    | exact superpose eq900 eq50
    | (have j1 := eq900 X0 (σ X1)
       grind)
    | exact resolve eq50 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq29805 : ∀ X0 X1 : G, (M.op X0 (τ (σ X1))) = (k (τ (σ (M.op (τ (σ X1)) X0))) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (M.op (τ (σ X1)) X0) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29762 X0 X1
       have i₂ := eq10 (M.op X0 (τ (σ X1)))
       grind)
    | exact superpose eq10 eq29762
    | (have j0 := eq29762 X0 X1
       grind)
    | exact resolve eq29762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29762
  have eq29926 : ∀ X0 X1 : G, (M.op X0 (τ (σ X1))) = (k (M.op (τ (σ X1)) X0) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (M.op (τ (σ X1)) X0) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29805 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) X0)
       grind)
    | exact superpose eq10 eq29805
    | (have j0 := eq29805 X0 X1
       grind)
    | exact resolve eq29805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29805
  have eq30037 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X0) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (M.op (τ (σ X1)) X0) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29926 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29926
    | (have j0 := eq29926 X0 X1
       grind)
    | exact resolve eq29926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29926
  have eq30123 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k (M.op X1 X0) X1) ∨ (M.op (τ (σ X1)) X0) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30037 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30037
    | (have j0 := eq30037 X0 X1
       grind)
    | exact resolve eq30037 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30037
  have eq30170 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = (τ (k (σ X1) (σ X1))) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30123 X0 X1
       have i₂ := eq12465 (σ X1)
       grind)
    | exact superpose eq12465 eq30123
    | (have j0 := eq30123 X0 X1
       grind)
    | exact resolve eq30123 eq12465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30123
  have eq30211 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = (k (τ (σ X1)) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30170 X0 X1
       have i₂ := eq50 (σ X1) X1
       grind)
    | exact superpose eq50 eq30170
    | (have j0 := eq30170 X0 X1
       grind)
    | exact resolve eq30170 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30170
  have eq30235 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30211 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30211
    | (have j0 := eq30211 X0 X1
       grind)
    | exact resolve eq30211 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30211
  have eq30243 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30235 X0 X1
       have i₂ := eq12643 X1
       grind)
    | exact superpose eq12643 eq30235
    | (have j0 := eq30235 X0 X1
       grind)
    | exact resolve eq30235 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30235
  have eq284508 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ (k X0 X0)) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq23401 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23401
  have eq284513 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (k X0 X0)) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq284508 X0
       have i₂ := eq12643 X0
       grind)
    | exact superpose eq12643 eq284508
    | (have j0 := eq284508 X0
       grind)
    | exact resolve eq284508 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284508
  have eq284656 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq284513 X0
       have i₂ := eq12643 X0
       grind)
    | exact superpose eq12643 eq284513
    | (have j0 := eq284513 X0
       grind)
    | exact resolve eq284513 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284513
  have eq287617 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq284656 X0
       have i₂ := eq16018 X0
       grind)
    | exact superpose eq16018 eq284656
    | (have j1 := eq16018 X0
       grind)
    | (have r₁ := eq284656 X0
       have r₂ := eq16018 X0
       grind)
    | exact resolve eq284656 eq16018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16018 eq284656
  have eq287637 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq287617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287617
  have eq287638 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq287637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287637
  have eq509710 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq965 (σ y) (σ x)
       have i₂ := eq10804
       grind)
    | exact superpose eq10804 eq965
    | exact resolve eq965 eq10804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965 eq10804
  have eq509775 : (τ (k (σ y) (σ y))) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq509710
       have i₂ := eq12465 (σ y)
       grind)
    | exact superpose eq12465 eq509710
    | exact resolve eq509710 eq12465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12465 eq509710
  have eq509854 : y = (τ (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq509775
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq509775
    | exact resolve eq509775 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509775
  have eq509918 : y = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq509854
       have i₂ := eq50 (σ y) y
       grind)
    | exact superpose eq50 eq509854
    | exact resolve eq509854 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq509854
  have eq509954 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq509918
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq509918
    | exact resolve eq509918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509918
  have eq509955 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq509954
  have eq509974 : y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq509955
       have i₂ := eq12643 y
       grind)
    | exact superpose eq12643 eq509955
    | exact resolve eq509955 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12643 eq509955
  have eq509984 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq509974
       have i₂ := eq12920 y
       grind)
    | exact superpose eq12920 eq509974
    | exact resolve eq509974 eq12920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509974
  have eq510087 : ∀ X0 : G, x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq22 y y x
       have i₂ := eq509984
       grind)
    | exact superpose eq509984 eq22
    | exact resolve eq22 eq509984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510124 : x ≠ y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq509984
  have eq510503 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq22 y y x
       have i₂ := eq510087 X0
       grind)
    | exact superpose eq510087 eq22
    | (have j1 := eq510087 X1
       grind)
    | exact resolve eq22 eq510087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510087
  have eq512106 : ∀ X0 X1 X2 : G, (σ x) = (σ (M.op y y)) ∨ (M.op X0 x) = (M.op X1 x) ∨ y = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X1
       have i₂ := eq510503 (M.op x X0) X2
       grind)
    | exact superpose eq510503 eq9
    | (have j1 := eq510503 X0 X2
       grind)
    | exact resolve eq9 eq510503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538725 : ∀ X0 X1 X2 : G, (M.op y y) = (τ (σ x)) ∨ (M.op X0 x) = (M.op X1 x) ∨ y = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq512106 X0 X1 X2
       grind)
    | exact superpose eq512106 eq10
    | (have j1 := eq512106 X0 X1 X2
       grind)
    | exact resolve eq10 eq512106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512106
  have eq539236 : ∀ X0 X1 X2 : G, x = (M.op y y) ∨ (M.op X0 x) = (M.op X1 x) ∨ y = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538725 X0 X1 X2
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq538725
    | (have j0 := eq538725 X0 X1 X2
       grind)
    | exact resolve eq538725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538725
  have eq539604 : ∀ X0 X1 X2 X3 : G, x = (M.op X0 x) ∨ (M.op X1 x) = (M.op X2 x) ∨ y = (M.op X3 y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 y y X3
       have i₂ := eq539236 X0 X1 X2
       grind)
    | exact superpose eq539236 eq22
    | (have j1 := eq539236 X1 X2 X3
       grind)
    | exact resolve eq22 eq539236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq539236
  have eq546663 : ∀ X0 X1 X2 : G, x ≠ (M.op X1 x) ∨ (M.op X0 x) = (M.op X1 x) ∨ y = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | (have j0 := eq539604 X0 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546668 : ∀ X0 X1 X2 : G, y = (M.op X2 y) ∨ (M.op X0 x) = (M.op X1 x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq546663 X0 X1 X2
       have j1 := eq539604 X0 X0 X1 X2
       grind)
    | (have r₁ := eq546663 X0 X0 X2
       have r₂ := eq539604 X0 X1 X2 x
       grind)
    | exact resolve eq546663 eq539604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539604 eq546663
  have eq546840 : ∀ X1 X2 X3 : G, (σ y) = (M.op X1 (σ y)) ∨ (M.op X2 x) = (M.op X3 x) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq452 X2 y X2
       have i₂ := eq546668 x X1 X2
       grind)
    | exact superpose eq546668 eq452
    | (have j1 := eq546668 X2 X3 X2
       grind)
    | exact resolve eq452 eq546668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548964 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op X0 x) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq546840 (σ x) X0 X1
       grind)
    | exact superpose eq546840 eq16
    | (have j1 := eq546840 X1 X0 X1
       grind)
    | exact resolve eq16 eq546840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546840
  have eq553612 : ∀ X0 X1 X2 X3 : G, (σ y) ≠ (σ y) ∨ (M.op X0 x) = (M.op X1 x) ∨ (M.op X2 x) = (M.op X3 x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq548964 X0 X1
       have i₂ := eq546668 X2 X3 x
       grind)
    | exact superpose eq546668 eq548964
    | (have j0 := eq548964 X0 X1
       have j1 := eq546668 X0 X1 X2
       grind)
    | exact resolve eq548964 eq546668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546668 eq548964
  have eq553627 : ∀ X0 X1 X2 X3 : G, (M.op X0 x) = (M.op X1 x) ∨ (M.op X2 x) = (M.op X3 x) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq553612 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553612
  have eq555710 : ∀ X0 X1 X2 : G, (M.op X1 x) ≠ (M.op X2 x) ∨ (M.op X0 x) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq553627 X0 X2 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555711 : ∀ X0 X2 : G, (M.op X0 x) = (M.op X2 x) := by
    intro X0 X2
    first
    | (have j0 := eq555710 X0 x X2
       have j1 := eq553627 X0 X2 X0 X2
       grind)
    | (have r₁ := eq555710 X0 X0 x
       have r₂ := eq553627 X0 x X2 x
       grind)
    | (have r₁ := eq555710 X0 x X0
       have r₂ := eq553627 X0 x X2 x
       grind)
    | (have r₁ := eq555710 X0 X2 x
       have r₂ := eq553627 X0 x X2 x
       grind)
    | exact resolve eq555710 eq553627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553627 eq555710
  have eq557872 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12774 x
       have i₂ := eq555711 x X0
       grind)
    | (have i₁ := eq12774 x
       have i₂ := eq555711 X0 x
       grind)
    | exact superpose eq555711 eq12774
    | (have j0 := eq12774 x
       grind)
    | exact resolve eq12774 eq555711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555711
  have eq558209 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq557872 X0
       have i₂ := eq12920 x
       grind)
    | exact superpose eq12920 eq557872
    | (have j0 := eq557872 X0
       grind)
    | exact resolve eq557872 eq12920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557872
  have eq565509 : ∀ X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq558209 x
       have i₂ := eq510503 x X1
       grind)
    | exact superpose eq510503 eq558209
    | (have j1 := eq510503 x X1
       grind)
    | exact resolve eq558209 eq510503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510503 eq558209
  have eq565566 : ∀ X1 : G, (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op X1 y) := by
    intro X1
    first
    | (have j0 := eq565509 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565509
  have eq640646 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq419 y y
       have i₂ := eq565566 x
       grind)
    | exact superpose eq565566 eq419
    | (have j1 := eq565566 X0
       grind)
    | exact resolve eq419 eq565566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq565566
  have eq641219 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq640646 X0
       have j1 := eq12774 x
       grind)
    | (have r₁ := eq640646 X0
       have r₂ := eq12774 x
       grind)
    | exact resolve eq640646 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12774 eq640646
  have eq641294 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq641219 X0
       have i₂ := eq12920 x
       grind)
    | exact superpose eq12920 eq641219
    | (have j0 := eq641219 X0
       grind)
    | exact resolve eq641219 eq12920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641219
  have eq641350 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ (σ x) = (M.op X0 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq452 x x x
       have i₂ := eq641294 X0
       grind)
    | exact superpose eq641294 eq452
    | (have j1 := eq641294 X1
       grind)
    | exact resolve eq452 eq641294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641294
  have eq646937 : ∀ X1 X2 : G, (σ y) = (M.op X1 (σ y)) ∨ (σ x) = (M.op X2 (σ x)) := by
    intro X1 X2
    first
    | (have i₁ := eq452 X1 y X2
       have i₂ := eq641350 x X1
       grind)
    | exact superpose eq641350 eq452
    | (have j1 := eq641350 X2 X1
       grind)
    | exact resolve eq452 eq641350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq666797 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq646937 (σ x) X0
       grind)
    | exact superpose eq646937 eq16
    | (have j1 := eq646937 x X0
       grind)
    | exact resolve eq16 eq646937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646937
  have eq685389 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq666797 X0
       have i₂ := eq641350 X1 x
       grind)
    | exact superpose eq641350 eq666797
    | (have j0 := eq666797 X0
       have j1 := eq641350 X0 X1
       grind)
    | exact resolve eq666797 eq641350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641350 eq666797
  have eq685412 : ∀ X0 X1 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | (have j0 := eq685389 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685389
  have eq697374 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq685412 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685412
  have eq697375 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq697374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697374
  have eq699611 : ∀ X1 : G, (τ (σ x)) = (M.op X1 (τ (σ x))) := by
    intro X1
    first
    | (have i₁ := eq1001 x (σ x) x
       have i₂ := eq697375 x
       grind)
    | exact superpose eq697375 eq1001
    | exact resolve eq1001 eq697375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq699693 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13757 x
       have i₂ := eq697375 (σ (M.op x x))
       grind)
    | exact superpose eq697375 eq13757
    | exact resolve eq13757 eq697375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699805 : ∀ X1 : G, x = (M.op X1 x) := by
    intro X1
    first
    | (have i₁ := eq699611 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq699611
    | exact resolve eq699611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699611
  have eq700259 : ∀ X1 : G, (σ x) = (σ (k X1 x)) ∨ x = (M.op x X1) ∨ x = X1 := by
    intro X1
    first
    | (have i₁ := eq14723 x X1 x
       have i₂ := eq699805 X1
       grind)
    | exact superpose eq699805 eq14723
    | (have j0 := eq14723 x x X1
       grind)
    | exact resolve eq14723 eq699805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14723
  have eq700266 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = X0 ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30243 x x
       have i₂ := eq699805 x
       grind)
    | exact superpose eq699805 eq30243
    | exact resolve eq30243 eq699805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30243 eq699805
  have eq863333 : ∀ X0 : G, (τ (σ x)) = (k X0 x) ∨ x = (M.op x X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 x)
       have i₂ := eq700259 X0
       grind)
    | exact superpose eq700259 eq10
    | (have j1 := eq700259 X0
       grind)
    | exact resolve eq10 eq700259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700259
  have eq863917 : ∀ X0 : G, x = (k X0 x) ∨ x = (M.op x X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq863333 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq863333
    | (have j0 := eq863333 X0
       grind)
    | exact resolve eq863333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863333
  have eq868717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq269
       have i₂ := eq700266 y
       grind)
    | exact superpose eq700266 eq269
    | (have j1 := eq700266 y
       grind)
    | exact resolve eq269 eq700266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq700266
  have eq869093 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq868717
  have eq869258 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq869093
       have i₂ := eq697375 (σ y)
       grind)
    | exact superpose eq697375 eq869093
    | exact resolve eq869093 eq697375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869093
  have eq869394 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq869258
       have i₂ := eq12920 y
       grind)
    | exact superpose eq12920 eq869258
    | exact resolve eq869258 eq12920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869258
  have eq869458 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq869394
       have r₂ := eq510124
       grind)
    | exact resolve eq869394 eq510124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510124 eq869394
  have eq1792405 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13757 y
       have i₂ := eq869458
       grind)
    | exact superpose eq869458 eq13757
    | exact resolve eq13757 eq869458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869458
  have eq1792497 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1792405
       have i₂ := eq697375 (σ (M.op y y))
       grind)
    | exact superpose eq697375 eq1792405
    | exact resolve eq1792405 eq697375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792405
  have eq1792498 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1792497
  have eq1793080 : (σ x) = (σ (M.op y y)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq287638 y
       have i₂ := eq1792498
       grind)
    | exact superpose eq1792498 eq287638
    | exact resolve eq287638 eq1792498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1799560 : (M.op y y) = (τ (σ x)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1793080
       grind)
    | exact superpose eq1793080 eq10
    | exact resolve eq10 eq1793080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793080
  have eq1800190 : x = (M.op y y) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq1799560
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1799560
    | exact resolve eq1799560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799560
  have eq1803420 : (τ y) = (τ (k y x)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq287638 y
       have i₂ := eq1800190
       grind)
    | exact superpose eq1800190 eq287638
    | exact resolve eq287638 eq1800190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287638 eq1800190
  have eq1803543 : (τ y) = (τ (k y x)) := by grind
  clear eq1803420
  have eq1803595 : (k y x) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq1803543
       grind)
    | exact superpose eq1803543 eq11
    | exact resolve eq11 eq1803543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803543
  have eq1805146 : y = (k y x) := by
    first
    | (have i₁ := eq1803595
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq1803595
    | exact resolve eq1803595 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803595
  have eq1807917 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq863917 y
       have i₂ := eq1805146
       grind)
    | exact superpose eq1805146 eq863917
    | (have j0 := eq863917 y
       grind)
    | exact resolve eq863917 eq1805146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863917
  have eq1807965 : x = y ∨ x = (M.op x y) := by grind
  clear eq1807917
  have eq1808045 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1807965
       grind)
    | exact superpose eq1807965 eq16
    | exact resolve eq16 eq1807965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807965
  have eq1808220 : x = (M.op x y) := by
    first
    | (have r₁ := eq1808045
       have r₂ := eq12920 x
       grind)
    | exact resolve eq1808045 eq12920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12920 eq1808045
  have eq1810881 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op X0 (σ (k y x))) = (M.op X1 (σ (k y x))) := by
    intro X0 X1
    first
    | (have i₁ := eq27970 X0 X1
       have i₂ := eq1808220
       grind)
    | exact superpose eq1808220 eq27970
    | (have j0 := eq27970 X0 X1
       grind)
    | exact resolve eq27970 eq1808220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27970
  have eq1811032 : ∀ X0 X1 : G, (σ y) = (σ (M.op x x)) ∨ (M.op X0 (σ (k y x))) = (M.op X1 (σ (k y x))) := by
    intro X0 X1
    first
    | (have j0 := eq1810881 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810881
  have eq1811060 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (M.op X0 (σ (k y x))) = (M.op X1 (σ (k y x))) := by
    intro X0 X1
    first
    | (have i₁ := eq1811032 X0 X1
       have i₂ := eq699693
       grind)
    | exact superpose eq699693 eq1811032
    | (have j0 := eq1811032 X0 X1
       grind)
    | exact resolve eq1811032 eq699693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699693 eq1811032
  have eq1811085 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1811060 X0 X1
       have i₂ := eq1805146
       grind)
    | exact superpose eq1805146 eq1811060
    | exact resolve eq1811060 eq1805146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805146 eq1811060
  have eq1827845 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1811085 X0 X1
       grind)
    | exact superpose eq1811085 eq16
    | (have j1 := eq1811085 X0 X1
       grind)
    | exact resolve eq16 eq1811085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811085
  have eq1828491 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1827845 X0 X1
       have i₂ := eq697375 (σ x)
       grind)
    | exact superpose eq697375 eq1827845
    | (have j0 := eq1827845 X0 X1
       grind)
    | exact resolve eq1827845 eq697375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697375 eq1827845
  have eq1828583 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1828491 X0 X1
       have i₂ := eq1808220
       grind)
    | exact superpose eq1808220 eq1828491
    | (have j0 := eq1828491 X0 X1
       grind)
    | exact resolve eq1828491 eq1808220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828491
  have eq1828584 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq1828583 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828583
  have eq1830028 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1828584 (σ x) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq1828584 X0 (σ x)
       grind)
    | exact superpose eq1828584 eq16
    | exact resolve eq16 eq1828584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828584
  have eq1830134 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1830028 X0
       have i₂ := eq1808220
       grind)
    | exact superpose eq1808220 eq1830028
    | exact resolve eq1830028 eq1808220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808220 eq1830028
  have eq1834168 : (σ x) ≠ (σ (M.op y y)) := by
    first
    | (have i₁ := eq1830134 (σ (M.op y y))
       have i₂ := eq13757 y
       grind)
    | exact superpose eq13757 eq1830134
    | exact resolve eq1830134 eq13757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13757 eq1830134
  have eq1834393 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1834168
       have i₂ := eq1792498
       grind)
    | exact superpose eq1792498 eq1834168
    | (have r₁ := eq1834168
       have r₂ := eq1792498
       grind)
    | exact resolve eq1834168 eq1792498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792498
  have eq1834484 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1834393
  have eq1834518 : False := by grind
  exact eq1834518
