import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq184 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq189 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq184
    | (have j0 := eq184 X0 X1
       grind)
    | exact resolve eq184 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq210 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq108 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq213 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq210 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq210
    | exact resolve eq210 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq9
    | exact resolve eq9 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq246 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq213 X0
       grind)
    | exact superpose eq213 eq9
    | exact resolve eq9 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq277 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq218
    | exact resolve eq218 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq305 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq277 X0 X1
       grind)
    | exact superpose eq277 eq9
    | exact resolve eq9 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4227 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq186
    | (have j0 := eq186 X1 X1
       grind)
    | exact resolve eq186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq4405 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4227 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4227
    | (have j0 := eq4227 (M.op X1 X1) X1
       grind)
    | exact resolve eq4227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4227
  have eq7649 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq189 x y
       grind)
    | exact superpose eq189 eq16
    | (have j1 := eq189 x (M.op x x)
       grind)
    | exact resolve eq16 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq29178 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7649
       have i₂ := eq4405 y x
       grind)
    | exact superpose eq4405 eq7649
    | (have j1 := eq4405 (M.op x x) x
       grind)
    | (have r₁ := eq7649
       have r₂ := eq4405 y x
       grind)
    | (have r₁ := eq7649
       have r₂ := eq4405 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq7649
       have r₂ := eq4405 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq7649 eq4405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4405 eq7649
  have eq29179 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq29178
  have eq29219 : (M.op x x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq29179
       grind)
    | exact superpose eq29179 eq10
    | exact resolve eq10 eq29179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29179
  have eq29313 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq29219
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29219
    | exact resolve eq29219 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29219
  have eq29314 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29313
  have eq29457 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq29314
       grind)
    | exact superpose eq29314 eq9
    | exact resolve eq9 eq29314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29474 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq305 x x x
       have i₂ := eq29314
       grind)
    | exact superpose eq29314 eq305
    | exact resolve eq305 eq29314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq29314
  have eq29509 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq29474 X0
       have i₂ := eq277 x X0
       grind)
    | exact superpose eq277 eq29474
    | exact resolve eq29474 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq29474
  have eq30170 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq29457 X0
       have i₂ := eq29509 X0
       grind)
    | exact superpose eq29509 eq29457
    | exact resolve eq29457 eq29509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29457 eq29509
  have eq30262 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30170 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30170
  have eq30274 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq30262 X0
       grind)
    | exact superpose eq30262 eq10
    | (have j1 := eq30262 X0
       grind)
    | exact resolve eq10 eq30262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30262
  have eq30367 : ∀ X0 : G, x = y ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30274 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30274
    | (have j0 := eq30274 X0
       grind)
    | exact resolve eq30274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30274
  have eq30368 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30367
  have eq30408 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq246 x X0
       have i₂ := eq30368 x
       grind)
    | exact superpose eq30368 eq246
    | exact resolve eq246 eq30368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq30497 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq30368 X0
       grind)
    | exact superpose eq30368 eq9
    | exact resolve eq9 eq30368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32522 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq30497 X1 X0
       have i₂ := eq30368 X0
       grind)
    | exact superpose eq30368 eq30497
    | exact resolve eq30497 eq30368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30497
  have eq32689 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq32522 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32522
  have eq34954 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30408 X0
       have i₂ := eq32689 (σ x) X0
       grind)
    | exact superpose eq32689 eq30408
    | exact resolve eq30408 eq32689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30408 eq32689
  have eq35064 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq34954 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34954
  have eq35102 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq35064 (σ y)
       grind)
    | exact superpose eq35064 eq16
    | exact resolve eq16 eq35064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35064
  have eq35425 : (σ y) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq35102
       have i₂ := eq30368 y
       grind)
    | exact superpose eq30368 eq35102
    | exact resolve eq35102 eq30368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30368 eq35102
  have eq35426 : (σ y) ≠ (σ y) ∨ x = y := by grind
  clear eq35425
  have eq35427 : x = y := by grind
  clear eq35426
  have eq35428 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35427
       grind)
    | exact superpose eq35427 eq16
    | exact resolve eq16 eq35427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35427
  have eq35429 : False := by grind
  exact eq35429

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_y_pyy_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq66
    | exact resolve eq66 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq69
    | exact resolve eq69 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq213 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq329 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq50 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    grind
  have eq369 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq329 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq329 X0 X1
       grind)
    | exact superpose eq329 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq329 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq329 X1 X1
       grind)
    | exact resolve eq12 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq369 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq419 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (M.op X1 X1)
       have i₂ := eq353 X1 (τ X0)
       grind)
    | exact superpose eq353 eq39
    | exact resolve eq39 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq423 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq419
    | exact resolve eq419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq433 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq49 X0 X0 X0 X1
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 X1 (M.op X1 X1) X2
       have i₂ := eq50 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq50
  have eq622 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq213 (M.op X1 X1) X0
       have i₂ := eq353 X1 (σ X0)
       grind)
    | exact superpose eq353 eq213
    | exact resolve eq213 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq353
  have eq644 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq622
    | exact resolve eq622 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq4065 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq423 (σ (M.op X1 X1)) X1
       have i₂ := eq373 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq373 eq423
    | (have j1 := eq373 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq423 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq4077 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq644 (τ (M.op X1 X1)) X1
       have i₂ := eq373 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq373 eq644
    | (have j1 := eq373 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq644 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq644
  have eq4109 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4077 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4077
  have eq4113 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4065 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065
  have eq4234 : ∀ X0 X2 : G, (M.op (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq343 x X2
       have i₂ := eq4109 x X0
       grind)
    | exact superpose eq4109 eq343
    | exact resolve eq343 eq4109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109
  have eq4367 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq343 x X2
       have i₂ := eq4113 x X0
       grind)
    | exact superpose eq4113 eq343
    | exact resolve eq343 eq4113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq5384 : ∀ X0 X1 X3 : G, (M.op x (M.op X1 X1)) = (M.op y (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq433 y x (M.op x (M.op X1 X1)) X3
       have i₂ := eq442 X1 X0 x
       grind)
    | exact superpose eq442 eq433
    | exact resolve eq433 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq5390 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq5384 x X1 x
       have i₂ := eq454 x sF0 x
       grind)
    | exact superpose eq454 eq5384
    | exact resolve eq5384 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5384
  have eq5550 : ∀ X0 X1 X3 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq443 eq433
    | exact resolve eq433 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq5556 : ∀ X1 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq5550 x X1 x
       have i₂ := eq454 x sF4 x
       grind)
    | exact superpose eq454 eq5550
    | exact resolve eq5550 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5550
  have eq5595 : ∀ X1 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq5556 eq454
    | exact resolve eq454 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6609 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 (M.op X3 X3)) (M.op X4 X4)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq433 X2 X3 X0 x
       have i₂ := eq440 (M.op X2 (M.op X3 X3)) X0 X1 x X4
       grind)
    | (have i₁ := eq433 (M.op X1 X1) X1 X1 (M.op X4 X4)
       have i₂ := eq440 (M.op X4 X4) X1 (M.op X1 X1) X3 X4
       grind)
    | exact superpose eq440 eq433
    | exact resolve eq433 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6699 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq433 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq440 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq433 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq440 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq440 eq433
    | exact resolve eq433 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq440
  have eq6833 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6699 X0 X1 x X3 x
       have i₂ := eq454 x (M.op X0 X1) x
       grind)
    | exact superpose eq454 eq6699
    | exact resolve eq6699 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6699
  have eq6853 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6609 X0 X1 X2 x x
       have i₂ := eq454 x X2 x
       grind)
    | exact superpose eq454 eq6609
    | exact resolve eq6609 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq6609
  have eq20595 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq6833 (M.op X1 X2) X0 x
       grind)
    | (have i₁ := eq14 X0 X1 (M.op X1 X0)
       have i₂ := eq6833 (M.op X1 X0) (M.op X1 X0) x
       grind)
    | exact superpose eq6833 eq14
    | exact resolve eq14 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20631 : ∀ X0 : G, y = (M.op (M.op X0 (M.op (M.op x y) X0)) x) := by
    intro X0
    first
    | (have i₁ := eq47 x
       have i₂ := eq6833 sF0 x x
       grind)
    | (have i₁ := eq47 sF0
       have i₂ := eq6833 sF0 sF0 x
       grind)
    | exact superpose eq6833 eq47
    | exact resolve eq47 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq20639 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48 x
       have i₂ := eq6833 sF4 x x
       grind)
    | (have i₁ := eq48 sF4
       have i₂ := eq6833 sF4 sF4 x
       grind)
    | exact superpose eq6833 eq48
    | exact resolve eq48 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq6833
  have eq21214 : ∀ X0 : G, x = (M.op X0 (M.op (M.op y (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq6853 x x X0
       have i₂ := eq5390 x
       grind)
    | exact superpose eq5390 eq6853
    | exact resolve eq6853 eq5390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5390
  have eq21216 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq5556 eq6853
    | exact resolve eq6853 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556 eq6853
  have eq21597 : x = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y (M.op x y))) (σ x)) := by
    first
    | exact superpose eq21216 eq21214
    | exact resolve eq21214 eq21216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21214 eq21216
  have eq39693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq71 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq39694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq39693
    | exact resolve eq39693 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39693
  have eq39699 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq39694
       have r₂ := eq28
       grind)
    | exact resolve eq39694 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39694
  have eq39701 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq39699
    | exact resolve eq39699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39699
  have eq39838 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39701 eq20595
    | exact resolve eq20595 eq39701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39701
  have eq39842 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20639 eq39838
    | exact resolve eq39838 eq20639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20639 eq39838
  have eq39858 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq39842
       have i₂ := eq329 X0 sF3
       grind)
    | (have i₁ := eq39842
       have i₂ := eq329 sF3 x
       grind)
    | exact superpose eq329 eq39842
    | exact resolve eq39842 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39842
  have eq41407 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op (M.op x y) X0)) x) ∨ (σ x) = (σ y) ∨ (M.op X1 X1) = (σ x) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq20595 X0 x x
       have i₂ := eq39858 X1
       grind)
    | (have i₁ := eq20595 X0 X0 X0
       have i₂ := eq39858 X0
       grind)
    | exact superpose eq39858 eq20595
    | (have j1 := eq39858 X1
       grind)
    | exact resolve eq20595 eq39858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20595 eq39858
  have eq41412 : ∀ X1 : G, x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X1
    first
    | exact superpose eq20631 eq41407
    | (have j0 := eq41407 x X1
       grind)
    | exact resolve eq41407 eq20631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20631 eq41407
  have eq41479 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq343 y X0
       have i₂ := eq41412 X1
       grind)
    | exact superpose eq41412 eq343
    | (have j1 := eq41412 X1
       grind)
    | exact resolve eq343 eq41412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq41412
  have eq42576 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq41479 y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq41479
    | (have j0 := eq41479 y X0
       grind)
    | exact resolve eq41479 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41479
  have eq43217 : ∀ X1 : G, (M.op (τ (σ x)) X1) = X1 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq4234 x X1
       have i₂ := eq42576 x
       grind)
    | exact superpose eq42576 eq4234
    | exact resolve eq4234 eq42576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4234 eq42576
  have eq43462 : ∀ X1 : G, (M.op x X1) = X1 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq29 eq43217
    | exact resolve eq43217 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43217
  have eq43961 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19
       have i₂ := eq43462 y
       grind)
    | exact superpose eq43462 eq19
    | (have j1 := eq43462 y
       grind)
    | exact resolve eq19 eq43462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43462
  have eq44142 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq43961
  have eq44223 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq44142 eq30
    | exact resolve eq30 eq44142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq44142
  have eq44291 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq44223
    | exact resolve eq44223 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44223
  have eq44292 : y = (M.op x y) ∨ x = y := by grind
  clear eq44291
  have eq44567 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq44292 eq21
    | exact resolve eq21 eq44292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44657 : x = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq44292 eq21597
    | exact resolve eq21597 eq44292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21597 eq44292
  have eq44659 : x = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq5595 eq44657
    | exact resolve eq44657 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595 eq44657
  have eq44733 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq44567
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq44567
    | exact resolve eq44567 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44567
  have eq44735 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq44733 eq27
    | exact resolve eq27 eq44733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44733
  have eq44880 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq44659 eq4367
    | exact resolve eq4367 eq44659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44659
  have eq44996 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq44880 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44880
    | (have j0 := eq44880 X0
       grind)
    | exact resolve eq44880 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44880
  have eq46479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq44996 eq44735
    | exact resolve eq44735 eq44996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44735 eq44996
  have eq46661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq46479
  have eq46729 : x = y := by
    first
    | (have r₁ := eq46661
       have r₂ := eq28
       grind)
    | exact resolve eq46661 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46661
  have eq46738 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq46729
       grind)
    | exact superpose eq46729 eq19
    | exact resolve eq19 eq46729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq46739 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq46729
       grind)
    | exact superpose eq46729 eq25
    | exact resolve eq25 eq46729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq46729
  have eq46883 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq46739
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq46739
    | exact resolve eq46739 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq46739
  have eq46889 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq46883 eq27
    | exact resolve eq27 eq46883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq46883
  have eq46977 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq46738
       have i₂ := eq329 X0 x
       grind)
    | (have i₁ := eq46738
       have i₂ := eq329 x X0
       grind)
    | exact superpose eq329 eq46738
    | exact resolve eq46738 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq46738
  have eq48297 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46889 eq46977
    | exact resolve eq46977 eq46889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46889
  have eq48535 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4367 X0 (σ (M.op X0 X0))
       have i₂ := eq46977 (σ (M.op X0 X0))
       grind)
    | exact superpose eq46977 eq4367
    | exact resolve eq4367 eq46977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4367
  have eq48591 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq48535 x
       have i₂ := eq46977 x
       grind)
    | exact superpose eq46977 eq48535
    | exact resolve eq48535 eq46977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46977 eq48535
  have eq48815 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq48591
    | exact resolve eq48591 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq48591
  have eq48935 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq48297 eq28
    | exact resolve eq28 eq48297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq48297
  have eq49030 : False := by grind
  exact eq49030

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_pxx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  clear eq22
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq72
    | (have j0 := eq72 (σ X0) (σ X1)
       grind)
    | exact resolve eq72 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq44
    | (have j1 := eq72 x y
       grind)
    | exact resolve eq44 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq104
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq392 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X2
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op (M.op X1 X1) X0))
       have r₂ := eq53 X0 X1 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X1 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106 eq72
    | (have j0 := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq72 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq663
    | exact resolve eq663 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq667 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq664
       have r₂ := eq27
       grind)
    | exact resolve eq664 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq670 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq667 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq667
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq667
       grind)
    | exact resolve eq12 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op X0 X0)) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq667 eq14
    | exact resolve eq14 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq672 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq670
  have eq711 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (σ (k X2 X2)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X0 X0
       have i₂ := eq53 X0 X1 (σ X0)
       grind)
    | exact superpose eq53 eq88
    | exact resolve eq88 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq730 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (k X2 X2)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq711 X0 X1 X2
       have i₂ := eq405 X1 X0
       grind)
    | exact superpose eq405 eq711
    | (have j0 := eq711 X0 X1 X2
       grind)
    | exact resolve eq711 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq739 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (k X2 X2)) ∨ (M.op X0 X0) = (σ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq730 X0 x X2
       have i₂ := eq405 x X0
       grind)
    | exact superpose eq405 eq730
    | (have j0 := eq730 X0 x X2
       grind)
    | exact resolve eq730 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq757 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq672 eq106
    | exact resolve eq106 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq760 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq757
  have eq766 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq760 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq760
       grind)
    | exact resolve eq13 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq778 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq766 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq778 eq106
    | exact resolve eq106 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq926 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq921
  have eq932 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq926
    | exact resolve eq926 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq934 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq932
       have r₂ := eq27
       grind)
    | exact resolve eq932 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq942 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X0) = X1 ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq934 eq14
    | exact resolve eq14 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (σ (M.op x y)) X1)) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq934 eq53
    | exact resolve eq53 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq951 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op x y))) (M.op X1 X1)) = X0 ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq934 eq487
    | exact resolve eq487 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq952 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (σ (M.op x y))) = X0 ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq934 eq487
    | exact resolve eq487 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq953 : (σ x) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq934 eq671
    | exact resolve eq671 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq954 : (σ x) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq953
  have eq1061 : (σ y) = (M.op (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq954 eq942
    | exact resolve eq942 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1075 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ (M.op x y)) X0)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq942 eq942
    | exact resolve eq942 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq1083 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ (M.op x y)) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1075 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1092 : (σ y) = (M.op (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op y x) := by grind
  clear eq1061
  have eq1108 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1083 sF1
       have i₂ := eq392 X0 sF1
       grind)
    | (have i₁ := eq1083 sF1
       have i₂ := eq392 sF1 x
       grind)
    | exact superpose eq392 eq1083
    | exact resolve eq1083 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1263 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) = X0 ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq934 eq951
    | exact resolve eq951 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934 eq951
  have eq1318 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1263 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1551 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ (M.op x y)) X0)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1092 eq947
    | exact resolve eq947 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1553 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ (M.op x y))) = X0 ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1092 eq952
    | exact resolve eq952 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq1556 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1092 eq1108
    | exact resolve eq1108 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq1108
  have eq1562 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1556
  have eq1563 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ (M.op x y))) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1553 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1565 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ (M.op x y)) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1551 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1845 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1563 eq1318
    | exact resolve eq1318 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq1563
  have eq1853 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1845 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq1961 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1562 eq1565
    | exact resolve eq1565 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq1565
  have eq2001 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by grind
  clear eq1961
  have eq2435 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ (M.op x y))) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1853 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq2524 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2435 X0
       grind)
    | (have r₁ := eq2435 X0
       have r₂ := eq2001
       grind)
    | exact resolve eq2435 eq2001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001 eq2435
  have eq3756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2524 eq106
    | exact resolve eq106 eq2524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq2524
  have eq3770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq3756
  have eq3778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq3770
    | exact resolve eq3770 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770
  have eq3780 : x = (M.op y x) := by
    first
    | (have r₁ := eq3778
       have r₂ := eq27
       grind)
    | exact resolve eq3778 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778
  have eq3782 : ∀ X0 X1 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op x (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x y X1 X0
       have i₂ := eq3780
       grind)
    | exact superpose eq3780 eq52
    | exact resolve eq52 eq3780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq3780
  have eq4222 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq3782 x x
       have i₂ := eq392 X0 (M.op x (M.op x x))
       grind)
    | (have i₁ := eq3782 x x
       have i₂ := eq392 (M.op x (M.op x x)) X0
       grind)
    | exact superpose eq392 eq3782
    | exact resolve eq3782 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq4243 : ∀ X1 : G, (M.op y X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq405 (M.op x (M.op x x)) X1
       have i₂ := eq3782 x x
       grind)
    | exact superpose eq3782 eq405
    | exact resolve eq405 eq3782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782
  have eq4611 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq400 X0 x X2 X3
       have i₂ := eq405 x X0
       grind)
    | exact superpose eq405 eq400
    | (have j0 := eq400 X0 x X2 X3
       grind)
    | (have r₁ := eq400 (M.op X0 X0) x (M.op (M.op x x) (M.op X0 X0)) X3
       have r₂ := eq405 X0 (M.op (M.op x x) (M.op X0 X0))
       grind)
    | (have r₁ := eq400 X0 x (M.op (M.op X0 X0) (M.op X0 (M.op (M.op x x) X0))) X3
       have r₂ := eq405 X0 (M.op X0 (M.op (M.op x x) X0))
       grind)
    | exact resolve eq400 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq405
  have eq4612 : ∀ X2 X3 : G, y ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X2 X3
    first
    | (have i₁ := eq4611 x X2 X3
       have i₂ := eq4222 x
       grind)
    | exact superpose eq4222 eq4611
    | (have j0 := eq4611 x X2 X3
       grind)
    | (have r₁ := eq4611 x y X3
       have r₂ := eq4222 x
       grind)
    | exact resolve eq4611 eq4222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4611
  have eq4613 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq4612 y X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4612
  have eq4620 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq4613 x
       grind)
    | exact superpose eq4613 eq44
    | exact resolve eq44 eq4613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq4624 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op y y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq739 X0 y
       have i₂ := eq4613 y
       grind)
    | exact superpose eq4613 eq739
    | (have j0 := eq739 X0 (M.op y y)
       grind)
    | exact resolve eq739 eq4613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq4642 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4624 X0
       have i₂ := eq4243 y
       grind)
    | (have i₁ := eq4624 X0
       have i₂ := eq4243 (M.op y y)
       grind)
    | exact superpose eq4243 eq4624
    | (have j0 := eq4624 X0
       grind)
    | exact resolve eq4624 eq4243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243 eq4624
  have eq4643 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq4642 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4642
  have eq4648 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4620
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4620
    | exact resolve eq4620 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4620
  have eq4650 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4643 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4643
    | (have j0 := eq4643 X0
       grind)
    | exact resolve eq4643 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4643
  have eq4654 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4648
    | exact resolve eq4648 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4648
  have eq4655 : y = (σ y) := by
    first
    | (have i₁ := eq4650 x
       have i₂ := eq4222 x
       grind)
    | exact superpose eq4222 eq4650
    | exact resolve eq4650 eq4222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4222 eq4650
  have eq4657 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq4655 eq26
    | exact resolve eq26 eq4655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4885 : (σ (M.op x y)) = (k (σ x) y) := by
    first
    | exact superpose eq4655 eq4654
    | exact resolve eq4654 eq4655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654 eq4655
  have eq4886 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq4885
       have i₂ := eq4613 sF2
       grind)
    | exact superpose eq4613 eq4885
    | exact resolve eq4885 eq4613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4613 eq4885
  have eq4941 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4886 eq4657
    | exact resolve eq4657 eq4886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657 eq4886
  have eq4942 : False := by grind
  exact eq4942

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X2 X2)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1 x
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq35
    | (have j0 := eq35 X0 X1 x
       grind)
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq40 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq69 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op X1 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2
       have i₂ := eq25 X0 X1 (σ X2)
       grind)
    | exact superpose eq25 eq22
    | exact resolve eq22 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq97 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq103 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq89 X0 x X2
       have i₂ := eq97 x X0
       grind)
    | exact superpose eq97 eq89
    | exact resolve eq89 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq97
  have eq253 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq43
    | (have j0 := eq43 X0 X1
       have j1 := eq40 (σ (M.op X0 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq43 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43
  have eq3338 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq253 x y
       grind)
    | exact superpose eq253 eq16
    | (have j1 := eq253 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq253 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq253 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq253 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq3375 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3338
  have eq4204 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) (M.op X0 X0)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq3375
       grind)
    | exact superpose eq3375 eq9
    | exact resolve eq9 eq3375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3375
  have eq4241 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4204 x
       have i₂ := eq69 x x
       grind)
    | exact superpose eq69 eq4204
    | exact resolve eq4204 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq4204
  have eq4242 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq4241
  have eq9633 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4242
       grind)
    | exact superpose eq4242 eq10
    | exact resolve eq10 eq4242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4242
  have eq9676 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9633
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9633
    | exact resolve eq9633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9633
  have eq9677 : x = y := by grind
  clear eq9676
  have eq14325 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9677
       grind)
    | exact superpose eq9677 eq16
    | exact resolve eq16 eq9677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9677
  have eq14326 : False := by grind
  exact eq14326

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pyx_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq66 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ (M.op X0 X0))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq10
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X1 X1) X0
       have i₂ := eq9 X1 X1 X1
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op (M.op X2 X1) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X1 X2 X3 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq24 X0 X0 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq24 X1 X0 X2 X4
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X1 (M.op X1 X1) X2
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25
  have eq135 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq160 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq135 y x
       grind)
    | exact superpose eq135 eq16
    | (have j1 := eq135 y x
       grind)
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq211 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1
       have i₂ := eq98 (τ X1) X0
       grind)
    | (have i₁ := eq32 X1
       have i₂ := eq98 X0 (τ X1)
       grind)
    | exact superpose eq98 eq32
    | exact resolve eq32 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq98
  have eq253 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq211 X0 (M.op X1 X1)
       grind)
    | exact superpose eq211 eq9
    | exact resolve eq9 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq160
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq160
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq160
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq160
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq160 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq1089 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by grind
  clear eq1088
  have eq1627 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 X0 (σ (M.op X0 X0)) X1 X2
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq111
    | exact resolve eq111 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1721 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1627 X0 X1 X2
       have i₂ := eq253 (M.op X0 X0) (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2))
       grind)
    | exact superpose eq253 eq1627
    | exact resolve eq1627 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq2425 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))))) X3) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq66 (M.op X0 X0) X3 X4
       have i₂ := eq117 X0 X0 X1 X0 X2
       grind)
    | (have i₁ := eq66 (M.op X0 (M.op X4 X4)) X1 X2
       have i₂ := eq117 X0 X0 X4 X3 X4
       grind)
    | exact superpose eq117 eq66
    | exact resolve eq66 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq2430 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (σ (M.op X4 X4))) (M.op (M.op X5 X3) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq111 X4 X3 X5 (M.op X0 X0)
       have i₂ := eq117 X0 X0 X1 X0 X2
       grind)
    | (have i₁ := eq111 X0 X1 X2 (M.op X0 (M.op X4 X4))
       have i₂ := eq117 X0 X0 X4 X3 X4
       grind)
    | exact superpose eq117 eq111
    | exact resolve eq111 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq2472 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq113 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq117 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq113 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq117 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq117 eq113
    | exact resolve eq113 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq117
  have eq2563 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2472 X0 X1 x X3 x
       have i₂ := eq126 x (M.op X0 X1) x
       grind)
    | exact superpose eq126 eq2472
    | exact resolve eq2472 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472
  have eq2874 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq118 X0 X1 x x X4 X5
       have i₂ := eq126 x (M.op X0 X1) x
       grind)
    | exact superpose eq126 eq118
    | exact resolve eq118 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq126
  have eq4645 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (σ (M.op X4 X4))) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1721 X4 X3 (M.op X1 X1)
       have i₂ := eq2874 X0 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq2874 eq1721
    | exact resolve eq1721 eq2874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721 eq2874
  have eq17824 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1089
       grind)
    | exact superpose eq1089 eq16
    | exact resolve eq16 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq17825 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17824
       have r₂ := eq211 x (σ x)
       grind)
    | exact resolve eq17824 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17824
  have eq117334 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (σ (M.op (M.op X3 (M.op X4 X4)) (M.op X3 (τ (M.op X0 X0)))))) X1) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2425 X3 X4 (τ X0) X1 X2
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq2425
    | exact resolve eq2425 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2425
  have eq213861 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X2 X2) (σ (M.op X3 X3))) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))) = X1 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2430 X4 X5 X6 (M.op X2 X2) X3 X1
       have i₂ := eq2563 X1 X0 X2
       grind)
    | (have i₁ := eq2430 X0 X1 X2 (M.op X0 X1) X4 X1
       have i₂ := eq2563 X0 X1 X3
       grind)
    | exact superpose eq2563 eq2430
    | exact resolve eq2430 eq2563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430 eq2563
  have eq215800 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op (σ (M.op X3 X3)) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))) = X1 := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq213861 X0 X1 x X3 X4 X5 X6
       have i₂ := eq110 x (σ (M.op X3 X3))
       grind)
    | exact superpose eq110 eq213861
    | exact resolve eq213861 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq213861
  have eq216180 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6)))) = X1 := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq215800 X0 X1 x X4 X5 X6
       have i₂ := eq253 x (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))
       grind)
    | exact superpose eq253 eq215800
    | exact resolve eq215800 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq215800
  have eq3291664 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (σ x) (σ (M.op y y))) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216180 (σ x) (σ y) X0 X1 X2
       have i₂ := eq17825
       grind)
    | exact superpose eq17825 eq216180
    | exact resolve eq216180 eq17825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17825 eq216180
  have eq3291701 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3291664 x x x
       have i₂ := eq4645 x x x (σ x) y
       grind)
    | exact superpose eq4645 eq3291664
    | exact resolve eq3291664 eq4645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645 eq3291664
  have eq3291702 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq3291701
  have eq3292144 : y = (τ (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3291702
       grind)
    | exact superpose eq3291702 eq10
    | exact resolve eq10 eq3291702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291702
  have eq3292542 : x = y ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq3292144
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3292144
    | exact resolve eq3292144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3292144
  have eq3314779 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3292542
       grind)
    | exact superpose eq3292542 eq16
    | exact resolve eq16 eq3292542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3292542
  have eq3314780 : (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq3314779
       have r₂ := eq211 x (σ x)
       grind)
    | exact resolve eq3314779 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3314779
  have eq3332803 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op y x) (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (τ (M.op X2 X2)))))) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117334 X2 y y X0 X1
       have i₂ := eq3314780
       grind)
    | exact superpose eq3314780 eq117334
    | exact resolve eq117334 eq3314780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3314780
  have eq3332835 : x = y := by
    first
    | (have i₁ := eq3332803 x x x
       have i₂ := eq117334 x y x x x
       grind)
    | exact superpose eq117334 eq3332803
    | exact resolve eq3332803 eq117334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117334 eq3332803
  have eq3332889 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3332835
       grind)
    | exact superpose eq3332835 eq16
    | exact resolve eq16 eq3332835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332835
  have eq3332890 : False := by grind
  exact eq3332890

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pxx_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq540 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ X2 = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq56 X0 X1 X3
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X2 X3 : G, (M.op X2 X3) = (k X2 X3) ∨ X2 = X3 := by
    intro X2 X3
    first
    | (have j0 := eq540 x x X2 X3
       grind)
    | (have r₁ := eq540 x x X2 X3
       have r₂ := eq56 x x X2
       grind)
    | exact resolve eq540 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq540
  have eq1197 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq548 x y
       grind)
    | exact superpose eq548 eq49
    | (have j1 := eq548 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1221 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1197
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1197
    | exact resolve eq1197 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1222 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq1221
    | exact resolve eq1221 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1222 eq548
    | (have j0 := eq548 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq548 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq1222
  have eq1228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1226
    | exact resolve eq1226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1231 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1228
       have r₂ := eq28
       grind)
    | exact resolve eq1228 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1234 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1231 eq30
    | exact resolve eq30 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1231
  have eq1252 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1234
    | exact resolve eq1234 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1234
  have eq1253 : x = y := by grind
  clear eq1252
  have eq1256 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq19
    | exact resolve eq19 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1257 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq25
    | exact resolve eq25 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1253
  have eq1273 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1257
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1257
    | exact resolve eq1257 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1257
  have eq1276 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1273 eq27
    | exact resolve eq27 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1273
  have eq1339 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1276 eq68
    | exact resolve eq68 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1276
  have eq1367 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1339
       have i₂ := eq1256
       grind)
    | exact superpose eq1256 eq1339
    | exact resolve eq1339 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256 eq1339
  have eq1369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1367 eq15
    | exact resolve eq15 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1369
    | exact resolve eq1369 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1369
  have eq1393 : False := by grind
  exact eq1393

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq45 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq106 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq568 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq569 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq568 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq574 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq569 X0 X1
       have j1 := eq106 X0 X1
       grind)
    | (have r₁ := eq569 X0 X1
       have r₂ := eq106 X0 X1
       grind)
    | (have r₁ := eq569 X1 X1
       have r₂ := eq106 X1 X1
       grind)
    | exact resolve eq569 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq569
  have eq775 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq574 (σ X1) (σ X0)
       grind)
    | exact superpose eq574 eq15
    | exact resolve eq15 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq574 X1 X0
       grind)
    | exact superpose eq574 eq775
    | exact resolve eq775 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq775
  have eq782 : False := by grind
  exact eq782

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_pyx_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq60 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : x ≠ x ∨ (M.op x (M.op x y)) = (k (M.op x y) x) := by
    first
    | exact superpose eq54 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq54
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq55 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq55
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq69
  have eq71 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  clear eq67
  have eq74 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq60 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq60
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x (M.op x y)) = (M.op (M.op x y) x) := by grind
  clear eq74
  have eq78 : x = (k x (M.op x y)) := by
    first
    | exact superpose eq54 eq77
    | exact resolve eq77 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq77
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq62 eq13
    | (have j0 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq62
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq79
  have eq83 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq82
    | exact resolve eq82 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq94 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq62 eq70
    | exact resolve eq70 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq70
  have eq97 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq60 eq71
    | exact resolve eq71 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq71
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  clear eq44
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq106
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X0 X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq97
    | (have r₁ := eq97 X0 (M.op X0 X1)
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq97 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq97 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | (have j0 := eq97 y x
       grind)
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq133 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq137 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq78 eq45
    | exact resolve eq45 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq78
  have eq142 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq141
    | exact resolve eq141 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq143 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq11 sF2 sF1
       grind)
    | exact superpose eq11 eq142
    | (have j1 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq156 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq157 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
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
  have eq161 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq98 eq156
    | exact resolve eq156 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq162 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq161
    | exact resolve eq161 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq163 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq162
       have i₂ := eq11 sF1 sF2
       grind)
    | exact superpose eq11 eq162
    | (have j1 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq165 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq137
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq137
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : (σ (k y (k y y))) = (k (σ y) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq36 (k y y)
       have i₂ := eq137
       grind)
    | exact superpose eq137 eq36
    | exact resolve eq36 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq137
       grind)
    | exact superpose eq137 eq16
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq165
  have eq173 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq138
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq138
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq157 eq16
    | exact resolve eq16 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq204 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq158 eq16
    | exact resolve eq16 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (σ (k y (k (M.op x y) (M.op x y)))) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq158 eq36
    | exact resolve eq36 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq331 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op (τ X0) X1)
       have i₂ := eq121 (τ X0) X1
       grind)
    | exact superpose eq121 eq34
    | exact resolve eq34 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq341 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq331
    | exact resolve eq331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq698 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq727 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq698 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq698 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq698 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq698 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq736 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq727 X0 X1
       have j1 := eq97 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq727 X0 X1
       have r₂ := eq97 (σ X0) (σ X1)
       grind)
    | exact resolve eq727 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq727
  have eq743 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq736
    | (have j0 := eq736 X0 X1
       grind)
    | exact resolve eq736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq744 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq334
    | exact resolve eq334 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq5146 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq743 (τ X1) (τ X0)
       have i₂ := eq744 X0 X1
       grind)
    | exact superpose eq744 eq743
    | exact resolve eq743 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq5152 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq98 eq743
    | exact resolve eq743 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq5207 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ y) X0) ∨ (k (σ y) X0) = (M.op (σ (τ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq743 y (τ X0)
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq743
    | exact resolve eq743 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq5256 : ∀ X0 : G, (k (σ y) X0) ≠ X0 ∨ (k (σ y) X0) = (M.op (σ (τ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5207 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5207
    | (have j0 := eq5207 X0
       grind)
    | exact resolve eq5207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5207
  have eq5303 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq5152
    | exact resolve eq5152 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5152
  have eq5306 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5146 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5146
    | (have j0 := eq5146 X0 X1
       grind)
    | exact resolve eq5146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5146
  have eq5337 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ (τ X0)) (σ y)) ∨ (k (σ y) X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq5256 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5256
    | (have j0 := eq5256 X0
       grind)
    | exact resolve eq5256 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5256
  have eq5383 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5303
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5303
    | exact resolve eq5303 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq5386 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5306 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5306
    | (have j0 := eq5306 X0 X1
       grind)
    | exact resolve eq5306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5306
  have eq5415 : ∀ X0 : G, (k (σ y) X0) ≠ X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5337 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5337
    | (have j0 := eq5337 X0
       grind)
    | exact resolve eq5337 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5337
  have eq5458 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq20 eq5383
    | exact resolve eq5383 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5383
  have eq5459 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5386 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5386
    | (have j0 := eq5386 X0 X1
       grind)
    | exact resolve eq5386 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5386
  have eq5468 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5458
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5458
    | exact resolve eq5458 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5458
  have eq5469 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5459 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5459
    | (have j0 := eq5459 X0 X1
       grind)
    | exact resolve eq5459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5459
  have eq5476 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5469 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5469
    | (have j0 := eq5469 X0 X1
       grind)
    | exact resolve eq5469 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5469
  have eq5628 : ∀ X0 : G, (σ y) ≠ (σ (M.op (τ (σ y)) X0)) ∨ (σ y) = (M.op (σ (M.op (τ (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5415 (σ (M.op (τ sF3) x))
       have i₂ := eq341 sF3 x
       grind)
    | exact superpose eq341 eq5415
    | exact resolve eq5415 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq5415
  have eq5635 : ∀ X0 : G, (σ y) ≠ (σ (M.op y X0)) ∨ (σ y) = (M.op (σ (M.op (τ (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq29 eq5628
    | (have j0 := eq5628 X0
       grind)
    | exact resolve eq5628 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5628
  have eq5638 : ∀ X0 : G, (σ y) ≠ (σ (M.op y X0)) ∨ (σ y) = (M.op (σ (M.op y X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq29 eq5635
    | (have j0 := eq5635 X0
       grind)
    | exact resolve eq5635 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq6297 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq139 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq139
    | (have j0 := eq139 y
       grind)
    | exact resolve eq139 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq6318 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6297
  have eq6324 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6318
       have i₂ := eq137
       grind)
    | exact superpose eq137 eq6318
    | exact resolve eq6318 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6318
  have eq6346 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6324
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6324 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6324
  have eq6379 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6346 eq171
    | exact resolve eq171 eq6346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq6536 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq159
    | (have j0 := eq159 (M.op x y)
       grind)
    | exact resolve eq159 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq6556 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6536
  have eq6561 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq158 eq6556
    | exact resolve eq6556 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq6556
  have eq6590 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6561
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6561 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6561
  have eq6651 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6590 eq204
    | exact resolve eq204 eq6590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq9288 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq9288
    | exact resolve eq9288 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9288
  have eq9300 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq9289
       have r₂ := eq27
       grind)
    | exact resolve eq9289 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9289
  have eq9304 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq9300
    | exact resolve eq9300 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9300
  have eq9309 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9304 eq53
    | exact resolve eq53 eq9304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9304
  have eq9328 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq9309
    | exact resolve eq9309 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9309
  have eq9329 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9328
  have eq9333 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq9329
       grind)
    | exact superpose eq9329 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9329
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq9329
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9329
       grind)
    | exact resolve eq13 eq9329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9336 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq9329
       grind)
    | exact superpose eq9329 eq53
    | exact resolve eq53 eq9329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9329
  have eq9354 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9333
  have eq9355 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9336
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9336
    | exact resolve eq9336 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9336
  have eq9356 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9355
  have eq9357 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9354
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9354
    | exact resolve eq9354 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9354
  have eq9358 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9357
       have r₂ := eq111
       grind)
    | exact resolve eq9357 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq9357
  have eq9365 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9356 eq83
    | exact resolve eq83 eq9356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9356
  have eq9606 : (σ x) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq743 y x
       have i₂ := eq9358
       grind)
    | exact superpose eq9358 eq743
    | exact resolve eq743 eq9358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq9358
  have eq9609 : (σ x) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9606
    | exact resolve eq9606 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9606
  have eq9619 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9609
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9609
    | exact resolve eq9609 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9609
  have eq9625 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9619
    | exact resolve eq9619 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9619
  have eq9627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9625
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9625
    | exact resolve eq9625 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9625
  have eq9629 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9627
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9627
    | exact resolve eq9627 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9627
  have eq9632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9629
    | exact resolve eq9629 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9629
  have eq9634 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9632
       have r₂ := eq27
       grind)
    | exact resolve eq9632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9632
  have eq10463 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9365 eq108
    | exact resolve eq108 eq9365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq9365
  have eq10478 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq10463
  have eq13976 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq10478
       grind)
    | exact superpose eq10478 eq53
    | exact resolve eq53 eq10478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10478
  have eq14001 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13976
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13976
    | exact resolve eq13976 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13976
  have eq14002 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq14001
  have eq14440 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14002 eq28
    | exact resolve eq28 eq14002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq14501 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14002 eq5468
    | (have r₁ := eq5468
       have r₂ := eq14002
       grind)
    | exact resolve eq5468 eq14002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5468 eq14002
  have eq14544 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq14501
  have eq14590 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14440
    | exact resolve eq14440 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14440
  have eq14603 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14590 eq20
    | exact resolve eq20 eq14590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14612 : (σ (k y y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14590 eq138
    | exact resolve eq138 eq14590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq14629 : (σ (k y (k y y))) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14590 eq206
    | exact resolve eq206 eq14590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq14590
  have eq14681 : (σ (k y (k y y))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6590 eq14629
    | exact resolve eq14629 eq6590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6590 eq14629
  have eq14698 : (k (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14612
       have i₂ := eq137
       grind)
    | exact superpose eq137 eq14612
    | exact resolve eq14612 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq14612
  have eq14700 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14603
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14603
    | exact resolve eq14603 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14603
  have eq14711 : (k (σ y) (k (σ y) (σ y))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14681
       have i₂ := eq167
       grind)
    | exact superpose eq167 eq14681
    | exact resolve eq14681 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq14681
  have eq14725 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6346 eq14698
    | exact resolve eq14698 eq6346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14698
  have eq14736 : (k (σ y) (M.op (σ y) (σ y))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6346 eq14711
    | exact resolve eq14711 eq6346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14711
  have eq14749 : (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14736
       have i₂ := eq121 sF3 sF3
       grind)
    | exact superpose eq121 eq14736
    | exact resolve eq14736 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq14736
  have eq15187 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14700 eq26
    | exact resolve eq26 eq14700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17891 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14544 eq6651
    | exact resolve eq6651 eq14544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6651 eq14544
  have eq17991 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq17891
    | exact resolve eq17891 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17891
  have eq18535 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6346 eq172
    | exact resolve eq172 eq6346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq6346
  have eq19286 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17991 eq5476
    | (have r₁ := eq5476 (M.op x y) (M.op x y)
       have r₂ := eq17991
       grind)
    | exact resolve eq5476 eq17991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17991
  have eq19287 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq19286
  have eq19554 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq19287 eq14
    | exact resolve eq14 eq19287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19287
  have eq29226 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq18535
       grind)
    | exact superpose eq18535 eq16
    | exact resolve eq16 eq18535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18535
  have eq29281 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6379 eq29226
    | exact resolve eq29226 eq6379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29226
  have eq29286 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq29281
       have r₂ := eq13 y y
       grind)
    | exact resolve eq29281 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29281
  have eq37094 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15187 eq143
    | exact resolve eq143 eq15187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq37128 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq37094
       have r₂ := eq27
       grind)
    | exact resolve eq37094 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37094
  have eq37188 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq163 eq53
    | exact resolve eq53 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq37213 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq37188
  have eq53951 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37128 eq53
    | exact resolve eq53 eq37128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37128
  have eq60548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53951 eq15187
    | exact resolve eq15187 eq53951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53951
  have eq60587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60548
  have eq60590 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq60587
       have r₂ := eq27
       grind)
    | exact resolve eq60587 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60587
  have eq60986 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60590 eq55
    | exact resolve eq55 eq60590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq61134 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq60986 eq14
    | exact resolve eq14 eq60986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60986
  have eq2648597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq37213 eq15187
    | exact resolve eq15187 eq37213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15187 eq37213
  have eq2648934 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2648597
       have r₂ := eq27
       grind)
    | exact resolve eq2648597 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648597
  have eq2649068 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2648934 eq53
    | exact resolve eq53 eq2648934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648934
  have eq2649322 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2649068 eq14749
    | exact resolve eq14749 eq2649068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14749 eq2649068
  have eq2651339 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2649322
  have eq2653815 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2651339 eq14725
    | exact resolve eq14725 eq2651339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14725 eq2651339
  have eq2653993 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2653815
  have eq2671284 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2653993 eq61134
    | exact resolve eq61134 eq2653993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61134 eq2653993
  have eq2671294 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2671284
  have eq2671327 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2671294
    | exact resolve eq2671294 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671294
  have eq2681821 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60590 eq2671327
    | exact resolve eq2671327 eq60590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60590 eq2671327
  have eq2682071 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2681821
  have eq2682074 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2682071
    | exact resolve eq2682071 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2682071
  have eq2682076 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2682074 eq27
    | exact resolve eq27 eq2682074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2682074
  have eq2682808 : x = (M.op x y) := by
    first
    | (have r₁ := eq2682076
       have r₂ := eq14700
       grind)
    | exact resolve eq2682076 eq14700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14700 eq2682076
  have eq2682810 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2682808 eq20
    | exact resolve eq20 eq2682808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2684272 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2682810
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2682810
    | exact resolve eq2682810 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2682810
  have eq2684340 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2684272 eq83
    | exact resolve eq83 eq2684272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2684342 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2684272 eq94
    | exact resolve eq94 eq2684272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2684535 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2684272 eq9634
    | (have r₁ := eq9634
       have r₂ := eq2684272
       grind)
    | exact resolve eq9634 eq2684272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9634
  have eq2685990 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2684535
  have eq2686305 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2685990 eq27
    | exact resolve eq27 eq2685990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2690907 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2685990 eq2684340
    | exact resolve eq2684340 eq2685990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684340
  have eq2690908 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2685990 eq2684342
    | exact resolve eq2684342 eq2685990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684342 eq2685990
  have eq2695190 : (τ (σ (M.op x y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq2690907 eq196
    | exact resolve eq196 eq2690907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq2690907
  have eq2695473 : (τ (σ (M.op x y))) = (k x y) := by
    first
    | exact superpose eq2682808 eq2695190
    | exact resolve eq2695190 eq2682808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2695190
  have eq2695494 : (M.op x y) = (k x y) := by
    first
    | exact superpose eq30 eq2695473
    | exact resolve eq2695473 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2695473
  have eq2695503 : x = (k x y) := by
    first
    | exact superpose eq2682808 eq2695494
    | exact resolve eq2695494 eq2682808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2695494
  have eq2695918 : x ≠ y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq5476 x y
       have i₂ := eq2695503
       grind)
    | exact superpose eq2695503 eq5476
    | exact resolve eq5476 eq2695503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476 eq2695503
  have eq2732180 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq173 eq5638
    | exact resolve eq5638 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq5638
  have eq2732183 : (σ y) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have r₁ := eq2732180
       have r₂ := eq2690908
       grind)
    | exact resolve eq2732180 eq2690908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732180
  have eq2732186 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2690908 eq2732183
    | exact resolve eq2732183 eq2690908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2690908 eq2732183
  have eq2732187 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2682808 eq2732186
    | exact resolve eq2732186 eq2682808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732186
  have eq2732188 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2732187
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2732187
    | exact resolve eq2732187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732187
  have eq2732189 : x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2682808 eq2732188
    | exact resolve eq2732188 eq2682808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732188
  have eq2732190 : x = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2682808 eq2732189
    | exact resolve eq2732189 eq2682808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732189
  have eq2732191 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq2732190
       have r₂ := eq2695918
       grind)
    | exact resolve eq2732190 eq2695918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732190
  have eq2733713 : (τ (σ y)) = (k y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2732191 eq6379
    | exact resolve eq6379 eq2732191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6379 eq2732191
  have eq2736470 : (τ (σ y)) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2733713
       have i₂ := eq29286
       grind)
    | exact superpose eq29286 eq2733713
    | exact resolve eq2733713 eq29286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29286 eq2733713
  have eq2736935 : y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq2736470
    | exact resolve eq2736470 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2736470
  have eq2739342 : y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19554 y y
       have i₂ := eq2736935
       grind)
    | exact superpose eq2736935 eq19554
    | exact resolve eq19554 eq2736935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19554 eq2736935
  have eq2739374 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2682808 eq2739342
    | exact resolve eq2739342 eq2682808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739342
  have eq2740168 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2739374
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2739374
    | exact resolve eq2739374 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739374
  have eq2740659 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2682808 eq2740168
    | exact resolve eq2740168 eq2682808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2740168
  have eq2740877 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2740659
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2740659
    | exact resolve eq2740659 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2740659
  have eq2740878 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq2740877
  have eq2740975 : x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq2682808 eq2740878
    | exact resolve eq2740878 eq2682808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2740878
  have eq2741060 : x = (M.op y x) := by
    first
    | (have r₁ := eq2740975
       have r₂ := eq2695918
       grind)
    | exact resolve eq2740975 eq2695918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2695918 eq2740975
  have eq2741122 : y = (M.op x y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq2741060
       grind)
    | exact superpose eq2741060 eq53
    | exact resolve eq53 eq2741060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2741060
  have eq2741393 : y = (M.op x y) := by
    first
    | (have i₁ := eq2741122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2741122
    | exact resolve eq2741122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2741122
  have eq2741439 : x = y := by
    first
    | exact superpose eq2682808 eq2741393
    | exact resolve eq2741393 eq2682808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2682808 eq2741393
  have eq2741482 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2741439
       grind)
    | exact superpose eq2741439 eq24
    | exact resolve eq24 eq2741439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2741439
  have eq2742407 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2741482
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2741482
    | exact resolve eq2741482 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2741482
  have eq2742575 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2684272 eq2742407
    | exact resolve eq2742407 eq2684272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684272 eq2742407
  have eq2742674 : False := by grind
  exact eq2742674
