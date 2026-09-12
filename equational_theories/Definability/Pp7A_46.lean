import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2744`: `x = ((y ◇ y) ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pyx_Equation2744 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2744 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2744.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq3281 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq3339 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3281 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3281
    | (have j0 := eq3281 X0 X1
       grind)
    | exact resolve eq3281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281
  have eq7464 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq711
       have i₂ := eq3339 y x
       grind)
    | exact superpose eq3339 eq711
    | (have j1 := eq3339 y x
       grind)
    | (have r₁ := eq711
       have r₂ := eq3339 y x
       grind)
    | (have r₁ := eq711
       have r₂ := eq3339 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq711
       have r₂ := eq3339 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq711 eq3339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq3339
  have eq7465 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7464
  have eq16211 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7465
       grind)
    | exact superpose eq7465 eq16
    | exact resolve eq16 eq7465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7465
  have eq16212 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq16211
       have r₂ := eq22 x
       grind)
    | exact resolve eq16211 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16211
  have eq16216 : y = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq16212
       grind)
    | exact superpose eq16212 eq9
    | exact resolve eq9 eq16212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16212
  have eq16218 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16216
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq16216
    | exact resolve eq16216 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16216
  have eq16219 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16218
       grind)
    | exact superpose eq16218 eq16
    | exact resolve eq16 eq16218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16218
  have eq16220 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16219
       have r₂ := eq22 x
       grind)
    | exact resolve eq16219 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16219
  have eq16224 : (σ y) = (M.op (M.op (σ (M.op x x)) (σ (M.op x x))) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq106 x (σ y)
       have i₂ := eq16220
       grind)
    | exact superpose eq16220 eq106
    | exact resolve eq106 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq16220
  have eq16239 : (σ y) = (M.op (σ (M.op (M.op x x) (M.op x x))) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16224
       have i₂ := eq22 (M.op x x)
       grind)
    | exact superpose eq22 eq16224
    | exact resolve eq16224 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16224
  have eq16245 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16239
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq16239
    | exact resolve eq16239 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq16239
  have eq16246 : (σ x) = (σ y) := by grind
  clear eq16245
  have eq16253 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16246
       grind)
    | exact superpose eq16246 eq16
    | exact resolve eq16 eq16246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16254 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16246
       grind)
    | exact superpose eq16246 eq10
    | exact resolve eq10 eq16246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16246
  have eq16423 : x = y := by
    first
    | (have i₁ := eq16254
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16254
    | exact resolve eq16254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16254
  have eq16424 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16253
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq16253
    | exact resolve eq16253 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16253
  have eq16425 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16424
       have i₂ := eq16423
       grind)
    | exact superpose eq16423 eq16424
    | exact resolve eq16424 eq16423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16423 eq16424
  have eq16426 : False := by grind
  exact eq16426

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pxx_pyx_Equation2755 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X2 X2) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 (M.op (M.op X2 X2) (M.op X3 X0))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (M.op X1 X0) X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq32
    | exact resolve eq32 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq32 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X2 X0)
       have i₂ := eq32 X2 X0
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq34 (M.op X0 X0) X1
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq37 X0 (M.op X0 X0)
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq37 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X1 X1) X0
       have i₂ := eq37 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq37 eq34
    | exact resolve eq34 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq81 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq43 X0 X1
       grind)
    | (have i₁ := eq12 X2 X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq43 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq43 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq293 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X0
       have i₂ := eq43 X0 (σ X0)
       grind)
    | (have i₁ := eq91 X0 X0
       have i₂ := eq43 (σ X0) X1
       grind)
    | exact superpose eq43 eq91
    | exact resolve eq91 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq294 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq16
    | (have j1 := eq91 x y
       grind)
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq91 X0 X0
       grind)
    | exact superpose eq91 eq37
    | (have j1 := eq91 X0 X0
       grind)
    | exact resolve eq37 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq323 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq299 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq328 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq1067 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq328
    | (have j0 := eq328 X1 (M.op X0 X0)
       grind)
    | exact resolve eq328 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X1)
       have i₂ := eq328 X0 (τ X1)
       grind)
    | exact superpose eq328 eq18
    | (have j1 := eq328 X0 (τ X1)
       grind)
    | exact resolve eq18 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq1158 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1067 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1168 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1126 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1126
    | (have j0 := eq1126 X0 X1
       grind)
    | exact resolve eq1126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1198 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1168 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1168
    | (have j0 := eq1168 X0 X1
       grind)
    | exact resolve eq1168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq2618 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ (M.op (M.op X2 X2) (M.op (τ X1) X0)))) ∨ (τ X1) = (M.op (τ X1) (M.op (M.op X2 X2) (M.op (τ X1) X0))) ∨ (M.op (M.op X2 X2) (M.op (τ X1) X0)) = (M.op (M.op (M.op X2 X2) (M.op (τ X1) X0)) (M.op (M.op X2 X2) (M.op (τ X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 (M.op (M.op X2 X2) (M.op (τ X1) X0)) X1
       have i₂ := eq9 X0 X2 (τ X1)
       grind)
    | exact superpose eq9 eq92
    | (have j0 := eq92 (M.op (M.op X2 X2) (M.op (τ X1) X0)) X1
       grind)
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq2696 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ (M.op (τ X1) X0))) ∨ (τ X1) = (M.op (τ X1) (M.op (M.op X2 X2) (M.op (τ X1) X0))) ∨ (M.op (M.op X2 X2) (M.op (τ X1) X0)) = (M.op (M.op (M.op X2 X2) (M.op (τ X1) X0)) (M.op (M.op X2 X2) (M.op (τ X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2618 X0 X1 X2
       have i₂ := eq37 X2 (M.op (τ X1) X0)
       grind)
    | exact superpose eq37 eq2618
    | (have j0 := eq2618 X0 X1 X2
       grind)
    | exact resolve eq2618 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2618
  have eq2710 : ∀ X0 X1 X2 : G, (τ X1) = (M.op (τ X1) (M.op (τ X1) X0)) ∨ (σ X0) = (k X1 (σ (M.op (τ X1) X0))) ∨ (M.op (M.op X2 X2) (M.op (τ X1) X0)) = (M.op (M.op (M.op X2 X2) (M.op (τ X1) X0)) (M.op (M.op X2 X2) (M.op (τ X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2696 X0 X1 X2
       have i₂ := eq37 X2 (M.op (τ X1) X0)
       grind)
    | exact superpose eq37 eq2696
    | (have j0 := eq2696 X0 X1 X2
       grind)
    | exact resolve eq2696 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2696
  have eq2715 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X2 X2) (M.op (τ X1) X0)) ∨ (τ X1) = (M.op (τ X1) (M.op (τ X1) X0)) ∨ (σ X0) = (k X1 (σ (M.op (τ X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2710 X0 X1 X2
       have i₂ := eq38 (M.op (τ X1) X0) X2 (M.op X2 X2)
       grind)
    | exact superpose eq38 eq2710
    | (have j0 := eq2710 X0 X1 X2
       grind)
    | exact resolve eq2710 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710
  have eq2716 : ∀ X0 X1 X2 : G, (τ X1) = (M.op (τ X1) (M.op (τ X1) X0)) ∨ (M.op X2 X2) = (M.op (τ X1) X0) ∨ (σ X0) = (k X1 (σ (M.op (τ X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2715 X0 X1 X2
       have i₂ := eq37 X2 (M.op (τ X1) X0)
       grind)
    | exact superpose eq37 eq2715
    | (have j0 := eq2715 X0 X1 X2
       grind)
    | exact resolve eq2715 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2715
  have eq3748 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq294
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq294
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq294 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq3749 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq3748
  have eq10481 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ (k (τ X0) (τ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq323 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq323
    | (have j0 := eq323 (τ X0) X1
       grind)
    | exact resolve eq323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq10639 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10481 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq10481
    | (have j0 := eq10481 X0 X1
       grind)
    | exact resolve eq10481 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10481
  have eq10640 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10639 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10639
    | (have j0 := eq10639 X0 X1
       grind)
    | exact resolve eq10639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10639
  have eq11097 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (k X1 X1) X0
       have i₂ := eq10640 X1 (M.op X0 X0)
       grind)
    | exact superpose eq10640 eq59
    | (have j1 := eq10640 X1 X1
       grind)
    | exact resolve eq59 eq10640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq10640
  have eq11418 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12183 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X2) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq11097 X2 X0
       grind)
    | exact superpose eq11097 eq60
    | (have j1 := eq11097 X2 X0
       grind)
    | exact resolve eq60 eq11097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq11097
  have eq14408 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12183 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12183
  have eq14421 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14408 X0 X1
       have j1 := eq1198 X1 X0
       grind)
    | (have r₁ := eq14408 (k X1 X1) X0
       have r₂ := eq1198 X0 X1
       grind)
    | (have r₁ := eq14408 X1 X0
       have r₂ := eq1198 X0 X1
       grind)
    | (have r₁ := eq14408 (M.op X0 X0) X1
       have r₂ := eq1198 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14408 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq14408
  have eq14687 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11418 X2 X1
       have i₂ := eq14421 X1 X0
       grind)
    | exact superpose eq14421 eq11418
    | (have j0 := eq11418 X2 X1
       grind)
    | (have r₁ := eq11418 X0 (M.op X1 X1)
       have r₂ := eq14421 (M.op X1 X1) X1
       grind)
    | exact resolve eq11418 eq14421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11418 eq14421
  have eq47583 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32 y x
       have i₂ := eq3749
       grind)
    | exact superpose eq3749 eq32
    | exact resolve eq32 eq3749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3749
  have eq47613 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq14687 x (σ x) (σ x)
       grind)
    | (have r₁ := eq47583
       have r₂ := eq14687 y x x
       grind)
    | (have r₁ := eq47583
       have r₂ := eq14687 (σ x) (σ x) x
       grind)
    | (have r₁ := eq47583
       have r₂ := eq14687 x x x
       grind)
    | exact resolve eq47583 eq14687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47583
  have eq56685 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (M.op X2 X2) = (M.op (τ X0) X1) ∨ (σ X1) = (k X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 (τ X0) (M.op (τ X0) X1)
       have i₂ := eq2716 X1 X0 X2
       grind)
    | exact superpose eq2716 eq32
    | (have j1 := eq2716 X1 X0 (τ X0)
       grind)
    | exact resolve eq32 eq2716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq56715 : ∀ X0 X1 : G, (σ X1) = (k X0 (σ (M.op (τ X0) X1))) ∨ (M.op (τ X0) X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq56685 X0 X1 (τ X0)
       have j1 := eq14687 X0 (M.op (τ X0) X1) (τ X0)
       grind)
    | (have r₁ := eq56685 X0 (τ X0) x
       have r₂ := eq14687 (τ X0) (M.op (τ X0) (τ X0)) x
       grind)
    | (have r₁ := eq56685 X0 X1 x
       have r₂ := eq14687 (τ X0) (M.op (τ X0) X1) x
       grind)
    | (have r₁ := eq56685 X0 X1 X0
       have r₂ := eq14687 X0 (M.op (τ X0) X1) x
       grind)
    | exact resolve eq56685 eq14687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56685
  have eq812254 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ (M.op (τ (σ X1)) X0)))) ∨ (M.op (τ (σ X1)) X0) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (σ (M.op (τ (σ X1)) X0))
       have i₂ := eq56715 (σ X1) X0
       grind)
    | exact superpose eq56715 eq28
    | (have j1 := eq56715 (σ X1) X0
       grind)
    | exact resolve eq28 eq56715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq56715
  have eq812614 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (M.op (τ (σ X1)) X0)) ∨ (M.op (τ (σ X1)) X0) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq812254 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) X0)
       grind)
    | exact superpose eq10 eq812254
    | (have j0 := eq812254 X0 X1
       grind)
    | exact resolve eq812254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812254
  have eq813069 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (M.op X1 X0)) ∨ (M.op (τ (σ X1)) X0) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq812614 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq812614
    | (have j0 := eq812614 X0 X1
       grind)
    | exact resolve eq812614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812614
  have eq813216 : ∀ X0 X1 : G, (k X1 (M.op X1 X0)) = X0 ∨ (M.op (τ (σ X1)) X0) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq813069 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq813069
    | (have j0 := eq813069 X0 X1
       grind)
    | exact resolve eq813069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813069
  have eq813253 : ∀ X0 X1 : G, (k X1 (M.op X1 X0)) = X0 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq813216 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq813216
    | (have j0 := eq813216 X0 X1
       grind)
    | exact resolve eq813216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813216
  have eq823687 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X1) (M.op X2 X0)) X0) = X2 ∨ (M.op (M.op (M.op X1 X1) (M.op X2 X0)) (M.op (M.op X1 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq813253 X2 (M.op (M.op X1 X1) (M.op X2 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq813253
    | exact resolve eq813253 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823689 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op (M.op X1 X1) X2) X0) ∨ (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq813253 (M.op X2 X0) (M.op (M.op X1 X1) X0)
       have i₂ := eq38 X0 X1 X2
       grind)
    | exact superpose eq38 eq813253
    | exact resolve eq813253 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813253
  have eq824474 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq823689 X0 X1 X2
       have i₂ := eq37 X1 X2
       grind)
    | exact superpose eq37 eq823689
    | (have j0 := eq823689 X0 X1 X2
       grind)
    | exact resolve eq823689 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823689
  have eq824476 : ∀ X0 X1 X2 : G, (k (M.op X2 X0) X0) = X2 ∨ (M.op (M.op (M.op X1 X1) (M.op X2 X0)) (M.op (M.op X1 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq823687 X0 X1 X2
       have i₂ := eq37 X1 (M.op X2 X0)
       grind)
    | exact superpose eq37 eq823687
    | (have j0 := eq823687 X0 X1 X2
       grind)
    | exact resolve eq823687 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823687
  have eq824550 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq824474 X0 X1 X2
       have i₂ := eq38 X2 X1 (M.op X1 X1)
       grind)
    | exact superpose eq38 eq824474
    | (have j0 := eq824474 X0 X1 X2
       grind)
    | exact resolve eq824474 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824474
  have eq824552 : ∀ X0 X1 X2 : G, (k (M.op X2 X0) X0) = X2 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq824476 X0 X1 X2
       have i₂ := eq38 (M.op X2 X0) X1 (M.op X1 X1)
       grind)
    | exact superpose eq38 eq824476
    | (have j0 := eq824476 X0 X1 X2
       grind)
    | exact resolve eq824476 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824476
  have eq828536 : ∀ X0 : G, (σ y) = (k (σ y) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq824552 (σ x) X0 (σ y)
       have i₂ := eq47613
       grind)
    | exact superpose eq47613 eq824552
    | (have j0 := eq824552 (σ x) X0 x
       grind)
    | exact resolve eq824552 eq47613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47613 eq824552
  have eq829010 : ∀ X0 : G, (σ y) = (k (σ y) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq828536 X0
       have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq828536 (σ x)
       have r₂ := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq828536 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq828536 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828536
  have eq829225 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq81 x (σ x) (σ y)
       grind)
    | (have r₁ := eq829010 x
       have r₂ := eq81 x (σ x) x
       grind)
    | (have r₁ := eq829010 x
       have r₂ := eq81 y x x
       grind)
    | exact resolve eq829010 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829010
  have eq829334 : (σ y) = (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq829225
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq829225
    | exact resolve eq829225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829225
  have eq829386 : (k y x) = (τ (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq829334
       grind)
    | exact superpose eq829334 eq10
    | exact resolve eq10 eq829334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829334
  have eq829676 : y = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq829386
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq829386
    | exact resolve eq829386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829386
  have eq829690 : y = (k y x) := by
    first
    | (have j1 := eq81 x x y
       grind)
    | (have r₁ := eq829676
       have r₂ := eq81 y x x
       grind)
    | exact resolve eq829676 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq829676
  have eq831958 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq824550 x X0 y
       have i₂ := eq829690
       grind)
    | exact superpose eq829690 eq824550
    | (have j0 := eq824550 x X0 x
       grind)
    | exact resolve eq824550 eq829690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824550 eq829690
  have eq831977 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op (M.op X1 X1) y)) ∨ x = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 y X0 X1 x
       have i₂ := eq831958 X2
       grind)
    | exact superpose eq831958 eq31
    | (have j1 := eq831958 X2
       grind)
    | exact resolve eq31 eq831958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq831979 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq34 y x
       have i₂ := eq831958 X0
       grind)
    | exact superpose eq831958 eq34
    | (have j1 := eq831958 y
       grind)
    | exact resolve eq34 eq831958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq831958
  have eq832043 : x = (M.op y y) := by
    first
    | (have j0 := eq831979 y
       have j1 := eq14687 x x y
       grind)
    | (have r₁ := eq831979 x
       have r₂ := eq14687 y x x
       grind)
    | (have r₁ := eq831979 x
       have r₂ := eq14687 x x x
       grind)
    | exact resolve eq831979 eq14687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831979
  have eq832044 : ∀ X1 X2 : G, (M.op X1 X1) = x ∨ x = (M.op X2 X2) := by
    intro X1 X2
    first
    | (have i₁ := eq831977 x X1 X2
       have i₂ := eq38 y x (M.op X1 X1)
       grind)
    | exact superpose eq38 eq831977
    | (have j0 := eq831977 x X1 X1
       grind)
    | exact resolve eq831977 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq831977
  have eq832060 : ∀ X1 : G, (M.op X1 X1) = x := by
    intro X1
    first
    | (have j0 := eq832044 X1 X1
       have j1 := eq14687 x x X1
       grind)
    | (have r₁ := eq832044 x x
       have r₂ := eq14687 x x x
       grind)
    | (have r₁ := eq832044 X1 x
       have r₂ := eq14687 x x x
       grind)
    | exact resolve eq832044 eq14687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14687 eq832044
  have eq832836 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 y X0
       have i₂ := eq832043
       grind)
    | exact superpose eq832043 eq37
    | exact resolve eq37 eq832043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq832869 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1158 y X0
       have i₂ := eq832043
       grind)
    | exact superpose eq832043 eq1158
    | exact resolve eq1158 eq832043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq833145 : y = (M.op x y) := by
    first
    | (have i₁ := eq32 y y
       have i₂ := eq832043
       grind)
    | exact superpose eq832043 eq32
    | exact resolve eq32 eq832043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq832043
  have eq833322 : x = (σ x) := by
    first
    | (have i₁ := eq832869 x
       have i₂ := eq832060 x
       grind)
    | exact superpose eq832060 eq832869
    | exact resolve eq832869 eq832060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832060 eq832869
  have eq835895 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq833322
       grind)
    | exact superpose eq833322 eq16
    | exact resolve eq16 eq833322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833322
  have eq836299 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq835895
       have i₂ := eq832836 (σ y)
       grind)
    | exact superpose eq832836 eq835895
    | exact resolve eq835895 eq832836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832836 eq835895
  have eq836449 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq836299
       have i₂ := eq833145
       grind)
    | exact superpose eq833145 eq836299
    | exact resolve eq836299 eq833145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833145 eq836299
  have eq836450 : False := by grind
  exact eq836450

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_pxx_pxy_Equation2755 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2755 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 (M.op X1 X0) X1
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op X0 X0)
       have i₂ := eq177 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq208 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X0 X1
       have i₂ := eq181 (M.op X0 X0) X1
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq184 X0 (M.op X0 X0)
       grind)
    | exact superpose eq184 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq184 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 (M.op X1 X1) X0
       have i₂ := eq184 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq184 eq181
    | exact resolve eq181 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq212 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq220 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq218 X0 X1
       have i₂ := eq184 X0 X1
       grind)
    | exact superpose eq184 eq218
    | exact resolve eq218 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq236 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq208 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq208 X1 X0
       grind)
    | exact superpose eq208 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq208 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq208 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op X0 X0)
       have i₂ := eq220 X0 sF2
       grind)
    | exact superpose eq220 eq90
    | exact resolve eq90 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq339 : ∀ X0 : G, x = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq29 eq328
    | exact resolve eq328 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq478 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq220 X1 (τ X0)
       grind)
    | exact superpose eq220 eq34
    | exact resolve eq34 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq478
    | exact resolve eq478 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq516 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ (M.op X1 X1))
       have i₂ := eq506 (τ X0) X1
       grind)
    | exact superpose eq506 eq34
    | exact resolve eq34 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq535 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq516 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq516
    | exact resolve eq516 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq560 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq208 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq208 X0 X1
       grind)
    | exact superpose eq208 eq11
    | (have j0 := eq11 (k X1 X1) X0
       grind)
    | exact resolve eq11 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq208
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq220 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq220
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq220 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 : G, x = (k x (τ (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq339 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq339
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq591 : ∀ X0 X1 : G, (M.op (k X0 X1) X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq177
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq606 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq610 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq610 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq618 : ∀ X0 : G, x = (k x (τ (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq584 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq622 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq580 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq624 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq578 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq630 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq572 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq631 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq560 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq640 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq630 X0 X1
       have j1 := eq236 X0 X0 X1
       grind)
    | (have r₁ := eq630 X0 X0
       have r₂ := eq236 X0 (k X0 X0) x
       grind)
    | (have r₁ := eq630 X1 X1
       have r₂ := eq236 X1 X1 x
       grind)
    | (have r₁ := eq630 (M.op X0 X0) X1
       have r₂ := eq236 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact resolve eq630 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq630
  have eq652 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X1 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq12 (k X1 X1) X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq11 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq652 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq655 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq653 X0
       have i₂ := eq184 X0 (M.op X0 X0)
       grind)
    | exact superpose eq184 eq653
    | (have j0 := eq653 X0
       grind)
    | exact resolve eq653 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq656 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq654 X0 X1
       have j1 := eq611 X0
       grind)
    | (have r₁ := eq654 X0 (M.op (k X0 X0) (k X0 X0))
       have r₂ := eq611 (k X0 X0)
       grind)
    | (have r₁ := eq654 X0 X1
       have r₂ := eq611 X0
       grind)
    | exact resolve eq654 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq657 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq631 eq655
    | (have j0 := eq655 X0
       have j1 := eq631 X0 X0
       grind)
    | exact resolve eq655 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq721 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ y))) = (σ (k X0 (k y y))) := by
    intro X0
    first
    | exact superpose eq115 eq38
    | exact resolve eq38 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq738 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq831 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq738 X0 (M.op X1 X1)
       have i₂ := eq220 X1 (σ X0)
       grind)
    | exact superpose eq220 eq738
    | exact resolve eq738 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq861 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq831 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq831
    | exact resolve eq831 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq1408 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq640 (σ (M.op X0 X0)) X1
       have i₂ := eq506 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq506 eq640
    | (have j0 := eq640 (σ (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq640 (σ (M.op X1 X1)) X1
       have r₂ := eq506 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq640 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1409 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (k X1 (σ (σ (M.op X0 X0)))) = (M.op (σ (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq640 (σ (σ (M.op X0 X0))) X1
       have i₂ := eq535 (σ (σ (M.op X0 X0))) X0
       grind)
    | exact superpose eq535 eq640
    | (have j0 := eq640 (σ (σ (M.op X0 X0))) X1
       grind)
    | (have r₁ := eq640 (σ (σ (M.op X1 X1))) X1
       have r₂ := eq535 (σ (σ (M.op X1 X1))) X1
       grind)
    | exact resolve eq640 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1412 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq640 (τ (M.op X0 X0)) X1
       have i₂ := eq861 (τ (M.op X0 X0)) X0
       grind)
    | exact superpose eq861 eq640
    | (have j0 := eq640 (τ (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq640 (τ (M.op X1 X1)) X1
       have r₂ := eq861 (τ (M.op X1 X1)) X1
       grind)
    | exact resolve eq640 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq1421 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1412 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1424 : ∀ X0 X1 : G, (k X1 (σ (σ (M.op X0 X0)))) = (M.op (σ (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1409 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1425 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1408 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq1430 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1421 X0 X1
       have i₂ := eq861 X1 X0
       grind)
    | exact superpose eq861 eq1421
    | exact resolve eq1421 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq1421
  have eq1433 : ∀ X0 X1 : G, (M.op (σ (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1424 X0 X1
       have i₂ := eq535 X1 X0
       grind)
    | exact superpose eq535 eq1424
    | exact resolve eq1424 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq1424
  have eq1434 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1425 X0 X1
       have i₂ := eq506 X1 X0
       grind)
    | exact superpose eq506 eq1425
    | exact resolve eq1425 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq1425
  have eq1450 : (σ (k y y)) = (k (σ (k y y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 (k y y)
       have i₂ := eq657 y
       grind)
    | exact superpose eq657 eq40
    | (have j1 := eq657 y
       grind)
    | exact resolve eq40 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq1459 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1450
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq1450
    | exact resolve eq1450 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq1466 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1459
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1459
    | exact resolve eq1459 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq1529 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 (τ (M.op X1 X1)) X0
       have i₂ := eq1430 X1 (M.op X0 (τ (M.op X1 X1)))
       grind)
    | exact superpose eq1430 eq181
    | exact resolve eq181 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1617 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 (σ (M.op X1 X1)) X0
       have i₂ := eq1434 X1 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq1434 eq181
    | exact resolve eq181 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1618 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 (σ (M.op X1 X1)) X0
       have i₂ := eq1434 X1 (M.op X0 X0)
       grind)
    | exact superpose eq1434 eq217
    | exact resolve eq217 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1957 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1434 X0 (σ (M.op X1 X1))
       have i₂ := eq1617 (σ (M.op X0 X0)) X1
       grind)
    | exact superpose eq1617 eq1434
    | exact resolve eq1434 eq1617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq2015 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1618 X1 (σ (M.op X0 X0))
       have i₂ := eq1434 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq1434 eq1618
    | exact resolve eq1618 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq2351 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1618 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq1433 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq1433 eq1618
    | exact resolve eq1618 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2361 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1529 (σ (σ (M.op X1 X1))) X0
       have i₂ := eq1433 X1 (τ (M.op X0 X0))
       grind)
    | exact superpose eq1433 eq1529
    | exact resolve eq1529 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq3194 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1957 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq1433 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq1433 eq1957
    | exact resolve eq1957 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq3346 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2015 (σ (σ (M.op X0 X0))) X1
       have i₂ := eq1433 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq1433 eq2015
    | exact resolve eq2015 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433 eq2015
  have eq6692 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq603
       grind)
    | exact superpose eq603 eq40
    | exact resolve eq40 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq6693 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6692
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6692
    | exact resolve eq6692 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6692
  have eq6695 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq6693
    | exact resolve eq6693 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6693
  have eq10146 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq611 X1
       have i₂ := eq624 X1 X0
       grind)
    | exact superpose eq624 eq611
    | (have j0 := eq611 X1
       have j1 := eq624 X1 X1
       grind)
    | (have r₁ := eq611 (M.op X1 X1)
       have r₂ := eq624 (M.op X1 X1) X1
       grind)
    | exact resolve eq611 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq10173 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq10146 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10146
  have eq10402 : ∀ X0 X1 X2 : G, (k X1 (k X0 X0)) = X1 ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220 X2 X1
       have i₂ := eq631 X2 X0
       grind)
    | exact superpose eq631 eq220
    | (have j1 := eq631 X2 X0
       grind)
    | exact resolve eq220 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10560 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq631 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11530 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq656 X1 X2
       have i₂ := eq624 X1 X0
       grind)
    | exact superpose eq624 eq656
    | (have j0 := eq656 X1 X2
       have j1 := eq624 X1 X1
       grind)
    | (have r₁ := eq656 X0 (M.op X1 X1)
       have r₂ := eq624 X0 X1
       grind)
    | (have r₁ := eq656 X0 (M.op (k X0 X0) (k X0 X0))
       have r₂ := eq624 (k X0 X0) X1
       grind)
    | exact resolve eq656 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq11545 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq11530 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11530
  have eq11547 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X2 X1) = X2 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq10173 eq11545
    | (have j0 := eq11545 X0 X1 X2
       have j1 := eq10173 X0 X2
       grind)
    | (have r₁ := eq11545 X1 X1 X1
       have r₂ := eq10173 X0 X1
       grind)
    | (have r₁ := eq11545 X0 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq10173 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11545 X0 X1 X0
       have r₂ := eq10173 X0 (k X0 X1)
       grind)
    | exact resolve eq11545 eq10173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11545
  have eq38528 : ∀ X0 : G, (σ X0) = (k (σ X0) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq721 X0
       have i₂ := eq622 y X0
       grind)
    | exact superpose eq622 eq721
    | (have j1 := eq622 (σ y) (σ X0)
       grind)
    | exact resolve eq721 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq721
  have eq38702 : ∀ X0 : G, (σ X0) = (k (σ X0) (k (σ y) (σ y))) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq10402 eq38528
    | (have j0 := eq38528 X0
       have j1 := eq10402 (σ y) (σ X0) x
       grind)
    | exact resolve eq38528 eq10402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10402 eq38528
  have eq38859 : ∀ X0 : G, (k X0 (k (σ y) (σ y))) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq38702 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq38702
    | exact resolve eq38702 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38702
  have eq38912 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op X0 X0) = (k (σ y) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq38859 eq10560
    | (have j0 := eq10560 X0 (k (σ y) (σ y))
       grind)
    | (have r₁ := eq10560 X0 (k (σ y) (σ y))
       have r₂ := eq38859 (k (σ y) (σ y))
       grind)
    | exact resolve eq10560 eq38859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10560 eq38859
  have eq38930 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq38912 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38912
  have eq85109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6695 eq606
    | exact resolve eq606 eq6695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq6695
  have eq85116 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq85109
       have r₂ := eq27
       grind)
    | exact resolve eq85109 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85109
  have eq85122 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq631 eq85116
    | (have j1 := eq631 (σ y) (σ y)
       grind)
    | exact resolve eq85116 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq85116
  have eq85124 : (σ y) = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq624 eq85122
    | (have j1 := eq624 y x
       grind)
    | exact resolve eq85122 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq85122
  have eq85533 : x = (k x (τ (σ y))) ∨ y = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq618 y
       have i₂ := eq85124
       grind)
    | exact superpose eq85124 eq618
    | (have j0 := eq618 y
       grind)
    | exact resolve eq618 eq85124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq85124
  have eq85585 : x = (k x (τ (σ y))) ∨ y = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq85533
  have eq85622 : x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq85585
    | exact resolve eq85585 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq85585
  have eq85651 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | (have j1 := eq11547 x y x
       grind)
    | (have r₁ := eq85622
       have r₂ := eq11547 y x y
       grind)
    | (have r₁ := eq85622
       have r₂ := eq11547 y x x
       grind)
    | exact resolve eq85622 eq11547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11547 eq85622
  have eq85665 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq85651 eq1466
    | exact resolve eq1466 eq85651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466 eq85651
  have eq85732 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (k x y) := by grind
  clear eq85665
  have eq85791 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq85732 eq152
    | exact resolve eq152 eq85732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq85732
  have eq85794 : x = (k x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq85791
    | exact resolve eq85791 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq85791
  have eq85795 : y = (M.op y y) ∨ x = (k x y) := by grind
  clear eq85794
  have eq85824 : ∀ X0 : G, x = (k x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq220 y X0
       have i₂ := eq85795
       grind)
    | exact superpose eq85795 eq220
    | exact resolve eq220 eq85795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq85795
  have eq86249 : x ≠ x ∨ x = (k x y) := by
    first
    | (have j0 := eq85824 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85824
  have eq86250 : x = (k x y) := by grind
  clear eq86249
  have eq86263 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq86250
       grind)
    | exact superpose eq86250 eq40
    | exact resolve eq40 eq86250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq86264 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq86263
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86263
    | exact resolve eq86263 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86263
  have eq86680 : y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq591 x y
       have i₂ := eq86250
       grind)
    | exact superpose eq86250 eq591
    | (have j0 := eq591 x y
       grind)
    | exact resolve eq591 eq86250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86250
  have eq86752 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq86264 eq591
    | (have j0 := eq591 (σ x) (σ y)
       grind)
    | exact resolve eq591 eq86264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq86264
  have eq86874 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq10173 x (σ y)
       grind)
    | (have r₁ := eq86752
       have r₂ := eq10173 (σ x) (σ y)
       grind)
    | (have r₁ := eq86752
       have r₂ := eq10173 (σ y) (σ x)
       grind)
    | (have r₁ := eq86752
       have r₂ := eq10173 (σ y) (σ y)
       grind)
    | exact resolve eq86752 eq10173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86752
  have eq86901 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq10173 x y
       grind)
    | (have r₁ := eq86680
       have r₂ := eq10173 x y
       grind)
    | (have r₁ := eq86680
       have r₂ := eq10173 y x
       grind)
    | (have r₁ := eq86680
       have r₂ := eq10173 y y
       grind)
    | exact resolve eq86680 eq10173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10173 eq86680
  have eq87405 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq184 y X0
       have i₂ := eq86901
       grind)
    | exact superpose eq86901 eq184
    | exact resolve eq184 eq86901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87408 : ∀ X0 : G, (M.op X0 X0) = y ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq208 y X0
       have i₂ := eq86901
       grind)
    | exact superpose eq86901 eq208
    | exact resolve eq208 eq86901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87491 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2361 X0 y
       have i₂ := eq86901
       grind)
    | exact superpose eq86901 eq2361
    | exact resolve eq2361 eq86901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361
  have eq87503 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ (σ y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq3194 y X0
       have i₂ := eq86901
       grind)
    | exact superpose eq86901 eq3194
    | exact resolve eq3194 eq86901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3194
  have eq87608 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ (σ y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq87503 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87503
    | (have j0 := eq87503 X0
       grind)
    | exact resolve eq87503 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87503
  have eq87619 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq87491 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87491
    | (have j0 := eq87491 X0
       grind)
    | exact resolve eq87491 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87491
  have eq87692 : (σ y) = (σ (σ (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87408 eq87608
    | exact resolve eq87608 eq87408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87608
  have eq87700 : (τ y) = (σ (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87408 eq87619
    | exact resolve eq87619 eq87408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87408 eq87619
  have eq87721 : (σ y) = (σ (σ (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq87692
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87692
    | exact resolve eq87692 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87692
  have eq87735 : (σ y) = (σ (τ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87700 eq87721
    | exact resolve eq87721 eq87700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87700 eq87721
  have eq87742 : x = (M.op y y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq87735
       have i₂ := eq14 y
       grind)
    | exact superpose eq14 eq87735
    | exact resolve eq87735 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87735
  have eq87772 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq208 y X0
       have i₂ := eq87742
       grind)
    | exact superpose eq87742 eq208
    | exact resolve eq208 eq87742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq87829 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1618 X0 y
       have i₂ := eq87742
       grind)
    | exact superpose eq87742 eq1618
    | exact resolve eq1618 eq87742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618
  have eq87853 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ x))) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2351 y X0
       have i₂ := eq87742
       grind)
    | exact superpose eq87742 eq2351
    | exact resolve eq2351 eq87742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351
  have eq87874 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ (σ x)))) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3346 y X0
       have i₂ := eq87742
       grind)
    | exact superpose eq87742 eq3346
    | exact resolve eq3346 eq87742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq87913 : x = (k (σ y) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq38930 y
       have i₂ := eq87742
       grind)
    | exact superpose eq87742 eq38930
    | exact resolve eq38930 eq87742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87924 : y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq177 y y
       have i₂ := eq87742
       grind)
    | exact superpose eq87742 eq177
    | exact resolve eq177 eq87742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87742
  have eq87927 : x = (k (σ y) (σ y)) ∨ y = (σ y) := by grind
  clear eq87913
  have eq87931 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq87924
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87924
    | exact resolve eq87924 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87924
  have eq87968 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ (σ x)))) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq87874 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq87874
    | (have j0 := eq87874 X0
       grind)
    | exact resolve eq87874 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87874
  have eq87988 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ x))) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq87853 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq87853
    | (have j0 := eq87853 X0
       grind)
    | exact resolve eq87853 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87853
  have eq88007 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq87829 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq87829
    | (have j0 := eq87829 X0
       grind)
    | exact resolve eq87829 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87829
  have eq88061 : (k (σ y) (σ y)) = (σ (σ (σ (σ x)))) ∨ y = (σ y) := by
    first
    | exact superpose eq38930 eq87968
    | exact resolve eq87968 eq38930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38930 eq87968
  have eq88078 : x = (σ (σ (σ x))) ∨ y = (σ y) := by
    first
    | exact superpose eq87772 eq87988
    | exact resolve eq87988 eq87772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87772 eq87988
  have eq88111 : x = (σ (σ (σ (σ x)))) ∨ y = (σ y) := by
    first
    | exact superpose eq87927 eq88061
    | exact resolve eq88061 eq87927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87927 eq88061
  have eq88146 : x = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq88078 eq88111
    | exact resolve eq88111 eq88078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88078 eq88111
  have eq88165 : y = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq88146
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq88146
    | exact resolve eq88146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88146
  have eq88191 : x = (M.op (σ y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq187
       have i₂ := eq87931
       grind)
    | exact superpose eq87931 eq187
    | exact resolve eq187 eq87931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88268 : x = (M.op (σ y) (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq187
       have i₂ := eq88165
       grind)
    | exact superpose eq88165 eq187
    | exact resolve eq187 eq88165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq88327 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq86901
       have i₂ := eq88165
       grind)
    | exact superpose eq88165 eq86901
    | exact resolve eq86901 eq88165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86901 eq88165
  have eq88330 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq86874 eq88327
    | exact resolve eq88327 eq86874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86874 eq88327
  have eq88331 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by grind
  clear eq88330
  have eq92503 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq88007 x
       grind)
    | exact superpose eq88007 eq175
    | exact resolve eq175 eq88007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq88007
  have eq93009 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq92503
       have i₂ := eq177 sF2 sF4
       grind)
    | exact superpose eq177 eq92503
    | exact resolve eq92503 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92503
  have eq93697 : (σ (M.op x y)) ≠ (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq93009 eq27
    | exact resolve eq27 eq93009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93009
  have eq97263 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq88331 eq184
    | exact resolve eq184 eq88331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq88331
  have eq98344 : x = (M.op x y) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq97263 eq88268
    | exact resolve eq88268 eq97263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88268
  have eq98346 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq97263 eq190
    | exact resolve eq190 eq97263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97263
  have eq98548 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq98344
  have eq99262 : (σ (M.op x y)) ≠ (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq98346 eq27
    | exact resolve eq27 eq98346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98346
  have eq99264 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq98548
       grind)
    | exact superpose eq98548 eq18
    | exact resolve eq18 eq98548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98548
  have eq120760 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 y y
       have i₂ := eq87405 X0
       grind)
    | exact superpose eq87405 eq177
    | (have j1 := eq87405 X0
       grind)
    | exact resolve eq177 eq87405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq87405
  have eq120770 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq120760 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120760
    | (have j0 := eq120760 X0
       grind)
    | exact resolve eq120760 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq120760
  have eq120917 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq87931 eq120770
    | exact resolve eq120770 eq87931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87931 eq120770
  have eq121354 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120917 eq88191
    | exact resolve eq88191 eq120917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88191
  have eq121355 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120917 eq190
    | exact resolve eq190 eq120917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq120917
  have eq121561 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq121354
  have eq122073 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq121355 eq27
    | exact resolve eq27 eq121355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121355
  have eq122085 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq121561
       grind)
    | exact superpose eq121561 eq24
    | exact resolve eq24 eq121561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122166 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99264
       have i₂ := eq121561
       grind)
    | exact superpose eq121561 eq99264
    | exact resolve eq99264 eq121561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99264
  have eq122171 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq122166
  have eq122227 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq122085
    | exact resolve eq122085 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122085
  have eq122322 : (σ y) ≠ (σ y) ∨ y = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122227 eq93697
    | (have r₁ := eq93697
       have r₂ := eq122227
       grind)
    | exact resolve eq93697 eq122227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93697
  have eq122331 : y = (σ y) ∨ x = (M.op x y) := by grind
  clear eq122322
  have eq122332 : (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121561 eq122331
    | exact resolve eq122331 eq121561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121561 eq122331
  have eq122410 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122332 eq26
    | exact resolve eq26 eq122332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122578 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122171 eq122410
    | exact resolve eq122410 eq122171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122171 eq122410
  have eq122653 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122578 eq27
    | exact resolve eq27 eq122578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122578
  have eq122665 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122227 eq122653
    | exact resolve eq122653 eq122227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122227 eq122653
  have eq122666 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq122665
  have eq122667 : x = (M.op x y) := by
    first
    | (have r₁ := eq122666
       have r₂ := eq122332
       grind)
    | exact resolve eq122666 eq122332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122332 eq122666
  have eq122670 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq122667
       grind)
    | exact superpose eq122667 eq22
    | exact resolve eq22 eq122667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq122674 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq178
       have i₂ := eq122667
       grind)
    | exact superpose eq122667 eq178
    | exact resolve eq178 eq122667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq122839 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq122670 eq20
    | exact resolve eq20 eq122670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq123159 : (σ x) ≠ (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq122839 eq99262
    | (have r₁ := eq99262
       have r₂ := eq122839
       grind)
    | exact resolve eq99262 eq122839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99262
  have eq123163 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq122839 eq122073
    | (have r₁ := eq122073
       have r₂ := eq122839
       grind)
    | exact resolve eq122073 eq122839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122073
  have eq123166 : y = (M.op x y) := by grind
  clear eq123163
  have eq123167 : x = (σ x) := by grind
  clear eq123159
  have eq123168 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq123167
       have i₂ := eq122667
       grind)
    | exact superpose eq122667 eq123167
    | exact resolve eq123167 eq122667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122667 eq123167
  have eq123280 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq123166
       grind)
    | exact superpose eq123166 eq24
    | exact resolve eq24 eq123166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq123428 : (σ x) = (σ y) := by
    first
    | exact superpose eq122670 eq123280
    | exact resolve eq123280 eq122670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122670 eq123280
  have eq123453 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq123168 eq123428
    | exact resolve eq123428 eq123168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123428
  have eq123478 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq123168 eq26
    | exact resolve eq26 eq123168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq123674 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq123453 eq123478
    | exact resolve eq123478 eq123453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123453 eq123478
  have eq123728 : y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122674 eq123674
    | exact resolve eq123674 eq122674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122674 eq123674
  have eq123763 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123728
       have i₂ := eq123166
       grind)
    | exact superpose eq123166 eq123728
    | exact resolve eq123728 eq123166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123166 eq123728
  have eq124076 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq123763 eq27
    | exact resolve eq27 eq123763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq123763
  have eq124086 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq122839 eq124076
    | exact resolve eq124076 eq122839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122839 eq124076
  have eq124090 : False := by grind
  exact eq124090

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  clear eq60
  have eq131 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq213 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq219 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq131
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq131
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq228 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq219
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq219
    | exact resolve eq219 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq229 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq228
    | exact resolve eq228 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq230 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq229
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq229
    | exact resolve eq229 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq346 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq213
       have i₂ := eq86 X0 sF2
       grind)
    | (have i₁ := eq213
       have i₂ := eq86 sF2 x
       grind)
    | exact superpose eq86 eq213
    | exact resolve eq213 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq213
  have eq10865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq230 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq10866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq10865
    | exact resolve eq10865 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10865
  have eq10877 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq10866
       have r₂ := eq28
       grind)
    | exact resolve eq10866 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10866
  have eq10881 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq10877
    | exact resolve eq10877 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10877
  have eq10930 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq10881 eq56
    | exact resolve eq56 eq10881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10881
  have eq10935 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq58 eq10930
    | exact resolve eq10930 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq10930
  have eq10936 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10935
  have eq10974 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq10936
       grind)
    | exact superpose eq10936 eq56
    | exact resolve eq56 eq10936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq10936
  have eq10979 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq57 eq10974
    | exact resolve eq10974 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq10974
  have eq10980 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq10979
  have eq11003 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq10980 eq30
    | exact resolve eq30 eq10980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10980
  have eq11115 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq11003
    | exact resolve eq11003 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11003
  have eq11116 : x = y := by grind
  clear eq11115
  have eq11264 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq11116
       grind)
    | exact superpose eq11116 eq19
    | exact resolve eq19 eq11116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq11265 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq11116
       grind)
    | exact superpose eq11116 eq25
    | exact resolve eq25 eq11116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11116
  have eq11369 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11265
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11265
    | exact resolve eq11265 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11265
  have eq11395 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11369 eq27
    | exact resolve eq27 eq11369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11369
  have eq11845 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11395 eq346
    | exact resolve eq346 eq11395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq11395
  have eq11878 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11845
       have i₂ := eq11264
       grind)
    | exact superpose eq11264 eq11845
    | exact resolve eq11845 eq11264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11264 eq11845
  have eq12061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11878 eq15
    | exact resolve eq15 eq11878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11878
  have eq12100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12061
    | exact resolve eq12061 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq12061
  have eq12111 : False := by grind
  exact eq12111

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq67 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
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
  have eq129 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq216 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq225 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq216
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq216
    | exact resolve eq216 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq225
    | exact resolve eq225 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq227 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq226
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq226
    | exact resolve eq226 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq343 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
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
  clear eq86 eq210
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
  clear eq45 eq61
  have eq870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq227 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq870
    | exact resolve eq870 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq874 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq871
       have r₂ := eq28
       grind)
    | exact resolve eq871 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq876 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq874
    | exact resolve eq874 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq880 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq876 eq58
    | exact resolve eq58 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq876
  have eq904 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq880 eq343
    | exact resolve eq343 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq913 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq904
    | exact resolve eq904 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq1467 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq60 x x
       have i₂ := eq913
       grind)
    | exact superpose eq913 eq60
    | exact resolve eq60 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq913
  have eq1474 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1467
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1467
    | exact resolve eq1467 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1475 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1474
  have eq1481 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1475 eq30
    | exact resolve eq30 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1475
  have eq1505 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1481
    | exact resolve eq1481 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1481
  have eq1506 : x = (M.op x y) ∨ x = y := by grind
  clear eq1505
  have eq1510 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1506 eq21
    | exact resolve eq21 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1512 : y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1506 eq57
    | exact resolve eq57 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1506
  have eq1534 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1510
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1510
    | exact resolve eq1510 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1639 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq378 x X0
       have i₂ := eq1512
       grind)
    | exact superpose eq1512 eq378
    | exact resolve eq378 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq1512
  have eq1650 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1639 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1639
    | (have j0 := eq1639 X0
       grind)
    | exact resolve eq1639 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq2178 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq67 eq1650
    | exact resolve eq1650 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1650
  have eq2216 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq2178 eq28
    | exact resolve eq28 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq2225 : x = y := by
    first
    | (have r₁ := eq2216
       have r₂ := eq1534
       grind)
    | exact resolve eq2216 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534 eq2216
  have eq2226 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2225
       grind)
    | exact superpose eq2225 eq19
    | exact resolve eq19 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2227 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2225
       grind)
    | exact superpose eq2225 eq25
    | exact resolve eq25 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2225
  have eq2251 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2227
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2227
    | exact resolve eq2227 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2227
  have eq2362 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2251 eq27
    | exact resolve eq27 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2251
  have eq2652 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2362 eq343
    | exact resolve eq343 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq2362
  have eq2662 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2652
       have i₂ := eq2226
       grind)
    | exact superpose eq2226 eq2652
    | exact resolve eq2652 eq2226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226 eq2652
  have eq2892 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2662 eq15
    | exact resolve eq15 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2892
    | exact resolve eq2892 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2892
  have eq2940 : False := by grind
  exact eq2940

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq91 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
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
  have eq134 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq130
  have eq135 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq134
  have eq177 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
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
  have eq185 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
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
  have eq186 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq185
    | exact resolve eq185 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
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
  have eq254 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
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
  have eq344 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq210
       have i₂ := eq91 X0 sF2
       grind)
    | (have i₁ := eq210
       have i₂ := eq91 sF2 x
       grind)
    | exact superpose eq91 eq210
    | exact resolve eq210 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq210
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
  clear eq45 eq61
  have eq9609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq186 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq9610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq9609
    | exact resolve eq9609 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9609
  have eq9621 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq9610
       have r₂ := eq28
       grind)
    | exact resolve eq9610 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9610
  have eq9625 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq9621 eq60
    | exact resolve eq60 eq9621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq9621
  have eq9632 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq9625
    | exact resolve eq9625 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9625
  have eq9635 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq9632
       grind)
    | exact superpose eq9632 eq56
    | exact resolve eq56 eq9632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9632
  have eq9777 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq378 y X0
       have i₂ := eq9635
       grind)
    | exact superpose eq9635 eq378
    | exact resolve eq378 eq9635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq9635
  have eq9795 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9777 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9777
    | (have j0 := eq9777 X0
       grind)
    | exact resolve eq9777 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9777
  have eq10860 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq9795 eq27
    | (have j1 := eq9795 (σ y)
       grind)
    | exact resolve eq27 eq9795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9795
  have eq10889 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10860
  have eq10913 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10889 eq28
    | exact resolve eq28 eq10889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10915 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10889 eq67
    | exact resolve eq67 eq10889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq10889
  have eq11157 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10915 eq254
    | exact resolve eq254 eq10915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq10915
  have eq11205 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq11157
    | exact resolve eq11157 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11157
  have eq12674 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq11205
       grind)
    | exact superpose eq11205 eq56
    | exact resolve eq56 eq11205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq11205
  have eq12680 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12674
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12674
    | exact resolve eq12674 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12674
  have eq12702 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12680 eq30
    | exact resolve eq30 eq12680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12680
  have eq12828 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq12702
    | exact resolve eq12702 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12702
  have eq12829 : y = (M.op x y) ∨ x = y := by grind
  clear eq12828
  have eq12849 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12829 eq21
    | exact resolve eq21 eq12829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12955 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12849
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12849
    | exact resolve eq12849 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12849
  have eq13167 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12955 eq10913
    | (have r₁ := eq10913
       have r₂ := eq12955
       grind)
    | exact resolve eq10913 eq12955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10913 eq12955
  have eq13182 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq13167
  have eq13183 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq13182
  have eq13268 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq13183 eq29
    | exact resolve eq29 eq13183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13183
  have eq13414 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq13268
    | exact resolve eq13268 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq13268
  have eq13683 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq13414 eq12829
    | exact resolve eq12829 eq13414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12829 eq13414
  have eq13684 : x = y := by grind
  clear eq13683
  have eq13760 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq13684
       grind)
    | exact superpose eq13684 eq19
    | exact resolve eq19 eq13684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq13761 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq13684
       grind)
    | exact superpose eq13684 eq25
    | exact resolve eq25 eq13684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq13684
  have eq13863 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13761
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13761
    | exact resolve eq13761 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13761
  have eq14084 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13863 eq27
    | exact resolve eq27 eq13863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq13863
  have eq14568 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14084 eq344
    | exact resolve eq344 eq14084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq14084
  have eq14587 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14568
       have i₂ := eq13760
       grind)
    | exact superpose eq13760 eq14568
    | exact resolve eq14568 eq13760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13760 eq14568
  have eq14763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14587 eq15
    | exact resolve eq15 eq14587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14587
  have eq14802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq14763
    | exact resolve eq14763 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq14763
  have eq14813 : False := by grind
  exact eq14813

/-- `Equation2890`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pxx_pxy_Equation2890 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2890 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2890.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 (M.op x x)) x) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq351 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq351 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq354 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq352 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq352 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq352 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq365 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq354 (σ X0)
       grind)
    | exact superpose eq354 eq15
    | exact resolve eq15 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365 X0
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq365
    | exact resolve eq365 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq365
  have eq433 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq68
    | exact resolve eq68 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       have j1 := eq436 X0 X1
       grind)
    | (have r₁ := eq433 X0 X1
       have r₂ := eq436 X0 X1
       grind)
    | exact resolve eq433 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq436
  have eq778 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq440 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq440
    | exact resolve eq440 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq440 X1 (σ X0)
       grind)
    | exact superpose eq440 eq15
    | (have j1 := eq440 X1 (σ X0)
       grind)
    | exact resolve eq15 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq808 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq789 X0 X1
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq789
    | (have j0 := eq789 X0 X1
       grind)
    | exact resolve eq789 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq789
  have eq826 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq778 (τ X1) X0
       grind)
    | exact superpose eq778 eq19
    | (have j1 := eq778 (τ X1) X0
       grind)
    | exact resolve eq19 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq778
  have eq1202 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq826 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq826
    | exact resolve eq826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq1281 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1202 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1202
    | (have j0 := eq1202 X0 X1
       grind)
    | exact resolve eq1202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1686 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq808 x y
       grind)
    | exact superpose eq808 eq16
    | (have j1 := eq808 x y
       grind)
    | exact resolve eq16 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq1779 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1686
       have i₂ := eq1281 y x
       grind)
    | exact superpose eq1281 eq1686
    | (have j1 := eq1281 y x
       grind)
    | (have r₁ := eq1686
       have r₂ := eq1281 y x
       grind)
    | exact resolve eq1686 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq1686
  have eq1780 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1779
  have eq1787 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq68 x
       have i₂ := eq1780
       grind)
    | exact superpose eq1780 eq68
    | exact resolve eq68 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1793 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq438 x
       have i₂ := eq1780
       grind)
    | exact superpose eq1780 eq438
    | exact resolve eq438 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq1838 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1793
       grind)
    | exact superpose eq1793 eq16
    | exact resolve eq16 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793
  have eq1866 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1838
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq1838
    | exact resolve eq1838 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787 eq1838
  have eq1867 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1866
  have eq1868 : (σ y) = (σ (M.op x x)) := by grind
  clear eq1867
  have eq1909 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq438 x
       have i₂ := eq1868
       grind)
    | exact superpose eq1868 eq438
    | exact resolve eq438 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq1913 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1868
       grind)
    | exact superpose eq1868 eq10
    | exact resolve eq10 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868
  have eq1961 : y = (M.op x x) := by
    first
    | (have i₁ := eq1913
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1913
    | exact resolve eq1913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1913
  have eq1967 : y = (M.op x y) := by
    first
    | (have i₁ := eq68 x
       have i₂ := eq1961
       grind)
    | exact superpose eq1961 eq68
    | exact resolve eq68 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1961
  have eq2029 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1909
       grind)
    | exact superpose eq1909 eq16
    | exact resolve eq16 eq1909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909
  have eq2044 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2029
       have i₂ := eq1967
       grind)
    | exact superpose eq1967 eq2029
    | exact resolve eq2029 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967 eq2029
  have eq2045 : False := by grind
  exact eq2045

/-- `Equation2890`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_y_pxy_Equation2890 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2890 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2890.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 (M.op x x)) x) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq73 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq74 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq91
    | (have j0 := eq91 (σ X0) (σ X1)
       grind)
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq44
    | (have j1 := eq91 x y
       grind)
    | exact resolve eq44 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117 eq91
    | (have j0 := eq91 (σ x) (σ y)
       grind)
    | exact resolve eq91 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq137 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq37
  have eq223 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq126 eq51
    | exact resolve eq51 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq238 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq223 eq14
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq238
    | (have j0 := eq238 (σ y) (σ x)
       grind)
    | exact resolve eq238 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq276 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq52 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y x
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ y) (σ x)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op (M.op X0 X1) X2) X2) X0 X1
       have i₂ := eq52 X2 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126 eq248
    | exact resolve eq248 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq316 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq308
  have eq318 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq316
    | exact resolve eq316 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq319 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126 eq318
    | exact resolve eq318 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq327 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq319
  have eq354 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq327 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq327
       grind)
    | exact resolve eq13 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq327 eq52
    | exact resolve eq52 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq354 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq399 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq419 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq355 eq223
    | exact resolve eq223 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq425 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq419
  have eq428 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq425
    | exact resolve eq425 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq432 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq359 eq49
    | exact resolve eq49 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq444 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126 eq74
    | (have r₁ := eq74
       have r₂ := eq126
       grind)
    | exact resolve eq74 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq126
  have eq445 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq444
  have eq536 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X1 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq544 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq536 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq536 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq536 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq552 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq327 eq432
    | exact resolve eq432 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq432
  have eq556 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq552
  have eq558 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq556
    | exact resolve eq556 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq561 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91 x x
       have i₂ := eq558
       grind)
    | exact superpose eq558 eq91
    | (have j0 := eq91 x x
       grind)
    | exact resolve eq91 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq562 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq561
  have eq565 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq562
       grind)
    | exact superpose eq562 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq562
       grind)
    | exact resolve eq13 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq746 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq276 eq52
    | exact resolve eq52 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq428 eq14
    | exact resolve eq14 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1051 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq445 eq117
    | exact resolve eq117 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq1054 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1051
  have eq1062 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1054 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1054
       grind)
    | exact resolve eq13 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1071 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1071 eq117
    | exact resolve eq117 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1071
  have eq1112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1108
  have eq1117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq1112
    | exact resolve eq1112 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1119 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1117
       have r₂ := eq27
       grind)
    | exact resolve eq1117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1141 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1119 eq29
    | exact resolve eq29 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1141
    | exact resolve eq1141 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1191 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq1408 : ∀ X0 : G, (k X0 (τ (σ x))) = (τ (M.op (σ X0) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq359 eq399
    | exact resolve eq399 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq399
  have eq1422 : ∀ X0 : G, (k X0 x) = (τ (M.op (σ X0) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq1408
    | exact resolve eq1408 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1408
  have eq3288 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1422 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1422
    | exact resolve eq1422 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq4059 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq571 (τ X0)
       have i₂ := eq3288 X0
       grind)
    | exact superpose eq3288 eq571
    | exact resolve eq571 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq3288
  have eq4070 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4059 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4059
  have eq5564 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq542 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq542
    | (have j0 := eq542 x y
       grind)
    | exact resolve eq542 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq5609 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5564
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5564
    | exact resolve eq5564 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5564
  have eq5677 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq5609
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5609
    | exact resolve eq5609 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5609
  have eq5726 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq5677
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5677
    | exact resolve eq5677 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5677
  have eq5752 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5726
    | exact resolve eq5726 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5726
  have eq8239 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq856 eq230
    | exact resolve eq230 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq856
  have eq8272 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8239
       have i₂ := eq52 sF2 sF2
       grind)
    | exact superpose eq52 eq8239
    | exact resolve eq8239 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8239
  have eq9918 : (M.op y x) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4070
    | exact resolve eq4070 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4070
  have eq10026 : (σ (M.op y x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9918 eq15
    | exact resolve eq15 eq9918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9918
  have eq24407 : (M.op (M.op x y) y) = (M.op x (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq746
       have i₂ := eq562
       grind)
    | exact superpose eq562 eq746
    | exact resolve eq746 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq25195 : x = (M.op (M.op (M.op (M.op x y) y) y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24407 eq14
    | exact resolve eq14 eq24407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24407
  have eq25486 : x = (M.op (M.op (M.op y y) y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1178 eq25195
    | exact resolve eq25195 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq25195
  have eq25535 : x = (M.op (M.op (M.op y y) y) x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25486
       have r₂ := eq1191
       grind)
    | exact resolve eq25486 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191 eq25486
  have eq25760 : (M.op x x) = (M.op (M.op (M.op (M.op y y) y) y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq298 (M.op y y) y x
       have i₂ := eq25535
       grind)
    | exact superpose eq25535 eq298
    | exact resolve eq298 eq25535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25535
  have eq25806 : (M.op x x) = (M.op y (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25760
       have i₂ := eq52 y y
       grind)
    | exact superpose eq52 eq25760
    | exact resolve eq25760 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25760
  have eq25810 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25806
       have i₂ := eq562
       grind)
    | exact superpose eq562 eq25806
    | exact resolve eq25806 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq25806
  have eq25861 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq25810
  have eq25865 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10026
       have i₂ := eq25861
       grind)
    | exact superpose eq25861 eq10026
    | exact resolve eq10026 eq25861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10026 eq25861
  have eq25914 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq25865
  have eq25920 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25914
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25914
    | exact resolve eq25914 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25914
  have eq26090 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25920 eq223
    | exact resolve eq223 eq25920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq25920
  have eq26135 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26090
  have eq26147 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq26135
    | exact resolve eq26135 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26135
  have eq26937 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26147 eq8272
    | exact resolve eq8272 eq26147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8272 eq26147
  have eq26985 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26937
  have eq26993 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq26985
    | exact resolve eq26985 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26985
  have eq26996 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26993 eq27
    | exact resolve eq27 eq26993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26993
  have eq27162 : x = (M.op x y) := by
    first
    | (have r₁ := eq26996
       have r₂ := eq1119
       grind)
    | exact resolve eq26996 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq26996
  have eq27170 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq27162 eq20
    | exact resolve eq20 eq27162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27176 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq27162 eq73
    | (have r₁ := eq73
       have r₂ := eq27162
       grind)
    | exact resolve eq73 eq27162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq27187 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq27162 eq276
    | exact resolve eq276 eq27162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq27202 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq27176
  have eq27211 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq27187
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27187
    | exact resolve eq27187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27187
  have eq27222 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq27170
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27170
    | exact resolve eq27170 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27170
  have eq27225 : x = (M.op x x) := by
    first
    | exact superpose eq27162 eq27211
    | exact resolve eq27211 eq27162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27211
  have eq27316 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq27222 eq26
    | exact resolve eq26 eq27222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq27331 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27222 eq277
    | exact resolve eq277 eq27222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq27394 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27222 eq5752
    | exact resolve eq5752 eq27222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5752
  have eq27448 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq27394
       have r₂ := eq27
       grind)
    | exact resolve eq27394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27394
  have eq27468 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq27225
       grind)
    | exact superpose eq27225 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq27225
       grind)
    | exact resolve eq13 eq27225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27518 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq27468 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27468
  have eq27799 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq27518 x
       grind)
    | exact superpose eq27518 eq43
    | exact resolve eq43 eq27518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq27816 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq544 x X0
       have i₂ := eq27518 x
       grind)
    | exact superpose eq27518 eq544
    | (have j0 := eq544 x X0
       grind)
    | exact resolve eq544 eq27518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq27860 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq27816 X0
       have i₂ := eq27225
       grind)
    | exact superpose eq27225 eq27816
    | (have j0 := eq27816 X0
       grind)
    | exact resolve eq27816 eq27225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27816
  have eq27861 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq27860 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27860
  have eq27866 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq27799
       have i₂ := eq27225
       grind)
    | exact superpose eq27225 eq27799
    | exact resolve eq27799 eq27225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27799
  have eq27888 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq27861 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27861
    | (have j0 := eq27861 X0
       grind)
    | exact resolve eq27861 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27861
  have eq27890 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27222 eq27866
    | exact resolve eq27866 eq27222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27866
  have eq27903 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq27222 eq27888
    | exact resolve eq27888 eq27222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27888
  have eq27905 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq27890
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27890
    | exact resolve eq27890 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27890
  have eq27918 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27222 eq27905
    | exact resolve eq27905 eq27222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27905
  have eq27928 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27918 eq91
    | (have j0 := eq91 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq91 eq27918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27918
  have eq27937 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq27928
  have eq28065 : (k y (M.op x y)) = (τ (M.op (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq27903 eq90
    | exact resolve eq90 eq27903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq27903
  have eq28112 : (k y x) = (τ (M.op (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq27162 eq28065
    | exact resolve eq28065 eq27162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28065
  have eq28124 : (M.op y x) = (τ (M.op (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq28112
       have i₂ := eq27518 y
       grind)
    | exact superpose eq27518 eq28112
    | exact resolve eq28112 eq27518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27518 eq28112
  have eq30002 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq27202
       grind)
    | exact superpose eq27202 eq44
    | exact resolve eq44 eq27202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq27202
  have eq30024 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27222 eq30002
    | exact resolve eq30002 eq27222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30002
  have eq30031 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq30024
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30024
    | exact resolve eq30024 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30024
  have eq30064 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30031 eq91
    | (have j0 := eq91 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq91 eq30031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq30031
  have eq30072 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27316 eq30064
    | exact resolve eq30064 eq27316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30064
  have eq30076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27316 eq30072
    | exact resolve eq30072 eq27316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27316 eq30072
  have eq30079 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq30076
       have r₂ := eq27
       grind)
    | exact resolve eq30076 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30076
  have eq30184 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq30079
       grind)
    | exact superpose eq30079 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq30079
       grind)
    | exact resolve eq13 eq30079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30079
  have eq30234 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq30184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30184
  have eq30629 : (k (σ (M.op x y)) (σ y)) = (σ (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq137
       have i₂ := eq30234 sF0
       grind)
    | exact superpose eq30234 eq137
    | exact resolve eq137 eq30234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq30234
  have eq30679 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27162 eq30629
    | exact resolve eq30629 eq27162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30629
  have eq30697 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30679
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30679
    | exact resolve eq30679 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30679
  have eq30706 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq30697
    | exact resolve eq30697 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30697
  have eq30713 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq30706
       have r₂ := eq27448
       grind)
    | exact resolve eq30706 eq27448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27448 eq30706
  have eq30722 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq30713 eq27
    | exact resolve eq27 eq30713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq30808 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30713 eq27331
    | exact resolve eq27331 eq30713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27331 eq30713
  have eq30820 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq30808 eq298
    | exact resolve eq298 eq30808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30808
  have eq30883 : (σ (M.op x y)) = (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27937 eq30820
    | exact resolve eq30820 eq27937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30820
  have eq30995 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq30883 eq298
    | exact resolve eq298 eq30883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq30883
  have eq31058 : (σ (M.op x y)) = (M.op (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27937 eq30995
    | exact resolve eq30995 eq27937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27937 eq30995
  have eq31073 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq31058
       have i₂ := eq52 sF3 sF3
       grind)
    | exact superpose eq52 eq31058
    | exact resolve eq31058 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31058
  have eq31094 : (τ (σ (M.op x y))) = (M.op y x) := by
    first
    | exact superpose eq31073 eq28124
    | exact resolve eq28124 eq31073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28124 eq31073
  have eq31157 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq30 eq31094
    | exact resolve eq31094 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31094
  have eq31170 : x = (M.op y x) := by
    first
    | exact superpose eq27162 eq31157
    | exact resolve eq31157 eq27162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31157
  have eq31209 : y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq52 x y
       have i₂ := eq31170
       grind)
    | exact superpose eq31170 eq52
    | exact resolve eq52 eq31170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq31170
  have eq31267 : y = (M.op x y) := by
    first
    | (have i₁ := eq31209
       have i₂ := eq27225
       grind)
    | exact superpose eq27225 eq31209
    | exact resolve eq31209 eq27225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27225 eq31209
  have eq31284 : y = (M.op x y) := by
    first
    | (have i₁ := eq31267
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31267
    | exact resolve eq31267 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq31267
  have eq31294 : x = y := by
    first
    | exact superpose eq27162 eq31284
    | exact resolve eq31284 eq27162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27162 eq31284
  have eq31312 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq31294
       grind)
    | exact superpose eq31294 eq24
    | exact resolve eq24 eq31294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31294
  have eq31472 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31312
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31312
    | exact resolve eq31312 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31312
  have eq31506 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27222 eq31472
    | exact resolve eq31472 eq27222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27222 eq31472
  have eq31532 : False := by grind
  exact eq31532
