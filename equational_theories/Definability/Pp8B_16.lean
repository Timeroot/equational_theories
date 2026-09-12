import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1728 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq77 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq87
  have eq199 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq202 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq207 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq202 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq202 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq220 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       have j1 := eq77 X1 (σ X0)
       grind)
    | (have r₁ := eq207 X0 X0
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq207 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq207
  have eq230 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq220 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq220
    | (have j0 := eq220 X0 X1
       grind)
    | exact resolve eq220 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq237 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq231 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231
    | exact resolve eq231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq231 x y
       grind)
    | exact superpose eq231 eq16
    | exact resolve eq16 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq325 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq237 X0 (τ X1)
       grind)
    | exact superpose eq237 eq18
    | exact resolve eq18 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq237
  have eq340 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq325
    | exact resolve eq325 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq347 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq340 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq340
    | exact resolve eq340 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq359 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq248
       have i₂ := eq347 x y
       grind)
    | exact superpose eq347 eq248
    | exact resolve eq248 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq347
  have eq360 : False := by grind
  exact eq360

/-- `Equation177`: `x = (y ◇ y) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_x_pxy_Equation177 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law177 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law177.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X1)) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1) (M.op X0 X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : x = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op y y)) := by
    first
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq47 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq48 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq49 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq53 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq15
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq59 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq62 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq15
    | exact resolve eq15 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq84 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56
    | (have j0 := eq56 x
       grind)
    | exact resolve eq56 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq56
    | (have j0 := eq56 y
       grind)
    | exact resolve eq56 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq127 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq59 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq59
    | (have j0 := eq59 y
       grind)
    | exact resolve eq59 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq145 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq62
    | (have j0 := eq62 (M.op x y)
       grind)
    | exact resolve eq62 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq155 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
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
  have eq156 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq71 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq71
    | exact resolve eq71 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq174 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq84 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq84
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq319 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : (M.op x x) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq34 y (M.op x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq34
    | exact resolve eq34 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : y = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq547 eq34
    | exact resolve eq34 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq45 eq34
    | exact resolve eq34 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq567 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq562 eq34
    | exact resolve eq34 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq35
    | exact resolve eq35 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0))
       have i₂ := eq35 (M.op X1 X1) X0
       grind)
    | exact superpose eq35 eq34
    | exact resolve eq34 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq578
    | exact resolve eq578 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq628 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X0 X1) X1
       have i₂ := eq603 X1 X0
       grind)
    | exact superpose eq603 eq34
    | exact resolve eq34 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (k (M.op X1 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1) (M.op X0 X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (k X0 X1)) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : y = (M.op (M.op x y) (k x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq552
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq552
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq552 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : x = (M.op (k y y) (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq36
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq567
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq567
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq38
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq739
  have eq752 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq736
  have eq755 : x = (M.op (k y y) (M.op x y)) ∨ y = (M.op y y) := by grind
  clear eq730
  have eq758 : y = (M.op (M.op x y) (k x x)) ∨ x = (M.op x x) := by grind
  clear eq727
  have eq762 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq706 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq764 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq704 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq784 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq764 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq764 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq764 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq837 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq749 eq16
    | exact resolve eq16 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq838 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq39 eq837
    | exact resolve eq837 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq837
  have eq841 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq838
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq838 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq843 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq841 eq38
    | exact resolve eq38 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq845 : ∀ X0 : G, (M.op (M.op (σ y) X0) (k (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq841 eq628
    | exact resolve eq628 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : (M.op (M.op (M.op x y) (M.op x y)) x) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq755 eq16
    | exact resolve eq16 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq1005 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq37 eq1004
    | exact resolve eq1004 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1004
  have eq1007 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq1005
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1005 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1008 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (k y y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq44
    | exact resolve eq44 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1009 : x = (M.op (k y y) (M.op x y)) := by
    first
    | (have i₁ := eq36
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq36
    | exact resolve eq36 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1011 : ∀ X0 : G, (M.op (M.op y X0) (k y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq628 y X0
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq628
    | exact resolve eq628 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 : G, (M.op (k y y) (M.op X0 y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq16
    | exact resolve eq16 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1166 : (k (σ x) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq752 eq628
    | exact resolve eq628 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq1172 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq562 eq1166
    | exact resolve eq1166 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq1166
  have eq1174 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq1172
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq1172 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1179 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq1174 eq567
    | exact resolve eq567 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq1185 : ∀ X0 : G, (M.op (k (σ x) (σ x)) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq1174 eq16
    | exact resolve eq16 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1190 : (σ x) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq1174 eq16
    | exact resolve eq16 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1197 : (k (σ x) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1179 eq628
    | exact resolve eq628 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1285 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq52 x
       have i₂ := eq697
       grind)
    | exact superpose eq697 eq52
    | exact resolve eq52 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq1286 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1285
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1285
    | exact resolve eq1285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1288 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1286
    | exact resolve eq1286 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1290 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1288
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq1288
    | exact resolve eq1288 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq1288
  have eq1364 : (k x x) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq758 eq628
    | exact resolve eq628 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq1370 : (M.op x x) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq547 eq1364
    | exact resolve eq1364 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq1364
  have eq1372 : (M.op x x) = (k x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq1370
       have r₂ := eq13 x x
       grind)
    | exact resolve eq1370 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1376 : (M.op (M.op x y) (M.op x y)) = (M.op (k x x) (k y y)) := by
    first
    | (have i₁ := eq1008
       have i₂ := eq1372
       grind)
    | exact superpose eq1372 eq1008
    | exact resolve eq1008 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1377 : y = (M.op (M.op x y) (k x x)) := by
    first
    | (have i₁ := eq552
       have i₂ := eq1372
       grind)
    | exact superpose eq1372 eq552
    | exact resolve eq552 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq1383 : ∀ X0 : G, (M.op (k x x) (M.op X0 x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq1372
       grind)
    | exact superpose eq1372 eq16
    | exact resolve eq16 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : x = (M.op (k x x) (k x x)) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq1372
       grind)
    | exact superpose eq1372 eq16
    | exact resolve eq16 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1290 eq700
    | exact resolve eq700 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1546 : (τ (σ (M.op x y))) = (k x y) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1290 eq110
    | exact resolve eq110 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1551 : (M.op x y) = (k x y) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq1546
    | exact resolve eq1546 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq1552 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1545
       have r₂ := eq27
       grind)
    | exact resolve eq1545 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq1556 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq841 eq1552
    | exact resolve eq1552 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1569 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1556 eq174
    | exact resolve eq174 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1575 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1569
    | exact resolve eq1569 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1576 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1575
  have eq1589 : ∀ X0 : G, (M.op (M.op y X0) y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1011 X0
       have i₂ := eq1576
       grind)
    | exact superpose eq1576 eq1011
    | exact resolve eq1011 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1595 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq1576
       grind)
    | exact superpose eq1576 eq52
    | exact resolve eq52 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1596 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq784 y X0
       have i₂ := eq1576
       grind)
    | exact superpose eq1576 eq784
    | (have j0 := eq784 y X0
       grind)
    | (have r₁ := eq784 y x
       have r₂ := eq1576
       grind)
    | exact resolve eq784 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576
  have eq1599 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1596 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1601 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1595
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1595
    | exact resolve eq1595 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1604 : ∀ X0 : G, (M.op (k X0 y) y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1604_14 : ∀ X0 : G, (M.op (M.op y X0) y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f1604_15 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f1604_24 : X0 ≠ (M.op (k X0 y) y) := by grind
    have f1604_25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f1604_26 : y ≠ (M.op x y) := by grind
    have f1604_27 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ y = (M.op x y) := by
      intro X0
      first
      | (have j0 := f1604_15 X0
         grind)
      | (have r₁ := f1604_15 X0
         have r₂ := f1604_25
         grind)
      | exact resolve f1604_15 f1604_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1604_28 : ∀ X0 : G, (M.op (M.op y X0) y) = X0 ∨ y = (M.op x y) := by
      intro X0
      first
      | (have j0 := f1604_14 X0
         grind)
      | (have r₁ := f1604_14 X0
         have r₂ := f1604_25
         grind)
      | exact resolve f1604_14 f1604_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1604_29 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
      intro X0
      first
      | (have j0 := f1604_27 X0
         grind)
      | (have r₁ := f1604_27 X0
         have r₂ := f1604_26
         grind)
      | exact resolve f1604_27 f1604_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1604_30 : ∀ X0 : G, (M.op (M.op y X0) y) = X0 := by
      intro X0
      first
      | (have j0 := f1604_28 X0
         grind)
      | (have r₁ := f1604_28 X0
         have r₂ := f1604_26
         grind)
      | exact resolve f1604_28 f1604_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1604_31 : X0 ≠ (M.op (M.op y X0) y) := by
      first
      | (have i₁ := f1604_24
         have i₂ := f1604_29 X0
         grind)
      | exact superpose f1604_29 f1604_24
      | exact resolve f1604_24 f1604_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1604_32 : False := by
      first
      | (have r₁ := f1604_31
         have r₂ := f1604_30 X0
         grind)
      | exact resolve f1604_31 f1604_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1604_32
  clear eq1589 eq1599
  have eq1626 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1601 eq843
    | exact resolve eq843 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1635 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1601 eq784
    | (have j0 := eq784 (σ y) X0
       grind)
    | (have r₁ := eq784 (σ y) x
       have r₂ := eq1601
       grind)
    | exact resolve eq784 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1638 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1635 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq1847 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1638 eq1626
    | exact resolve eq1626 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626 eq1638
  have eq1874 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1847
  have eq1900 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1874 eq174
    | exact resolve eq174 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq1901 : x = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1900
    | exact resolve eq1900 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq1903 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1901 eq1604
    | exact resolve eq1604 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604 eq1901
  have eq1905 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1903
  have eq1907 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1905
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1905
    | exact resolve eq1905 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq1980 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0 (k X0 X0)
       have i₂ := eq762 X0 X0
       grind)
    | exact superpose eq762 eq34
    | (have j1 := eq762 X0 x
       grind)
    | exact resolve eq34 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq1990 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1980 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1980 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1980 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1907 eq14
    | exact resolve eq14 eq1907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq2125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2123
    | exact resolve eq2123 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123
  have eq2128 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2125
       have r₂ := eq27
       grind)
    | exact resolve eq2125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2129 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2128 eq27
    | exact resolve eq27 eq2128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2132 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2128 eq156
    | (have r₁ := eq156
       have r₂ := eq2128
       grind)
    | exact resolve eq156 eq2128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq2137 : (σ x) = (M.op (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2128 eq843
    | exact resolve eq843 eq2128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2141 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2132
  have eq2146 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq841 eq2141
    | exact resolve eq2141 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141
  have eq2395 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2146 eq174
    | exact resolve eq174 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2411 : (σ x) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq2395
    | exact resolve eq2395 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395
  have eq2478 : (σ (M.op x y)) = (σ x) ∨ y = (k y y) ∨ y = (M.op x y) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2411 eq1290
    | exact resolve eq1290 eq2411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq2483 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2411 eq174
    | exact resolve eq174 eq2411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq2486 : y = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq2478
  have eq2489 : x = (k x y) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2483
    | exact resolve eq2483 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483
  have eq2492 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1551 eq2489
    | exact resolve eq2489 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551 eq2489
  have eq2507 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq2486
       grind)
    | exact superpose eq2486 eq52
    | exact resolve eq52 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2520 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2507
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2507
    | exact resolve eq2507 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq2539 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq2492
       grind)
    | exact superpose eq2492 eq52
    | exact resolve eq52 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2552 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2539
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2539
    | exact resolve eq2539 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2539
  have eq2596 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2520 eq2137
    | exact resolve eq2137 eq2520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2613 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2596
  have eq2620 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq841 eq2613
    | exact resolve eq2613 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613
  have eq2676 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2552 eq2137
    | exact resolve eq2137 eq2552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq2693 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2676
  have eq2700 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq841 eq2693
    | exact resolve eq2693 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2693
  have eq2767 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2620 eq127
    | exact resolve eq127 eq2620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2783 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2620 eq2520
    | exact resolve eq2520 eq2620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520 eq2620
  have eq2795 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq2783
  have eq2824 : x = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq2767
    | exact resolve eq2767 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767
  have eq2837 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2795 eq31
    | exact resolve eq31 eq2795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2845 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2795 eq127
    | exact resolve eq127 eq2795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2795
  have eq2922 : (k x x) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq109 eq2845
    | exact resolve eq2845 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq2930 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2837
    | exact resolve eq2837 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837
  have eq2940 : y = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2486 eq2922
    | exact resolve eq2922 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922
  have eq2949 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2930 eq2940
    | exact resolve eq2940 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2940
  have eq3013 : (M.op x y) = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq2930 eq28
    | exact resolve eq28 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq3021 : (k (M.op x y) (M.op x y)) = (τ (k (σ x) (σ x))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq2930 eq145
    | exact resolve eq145 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq2930
  have eq3028 : (k x x) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq109 eq3021
    | exact resolve eq3021 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021
  have eq3036 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3013
    | exact resolve eq3013 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3013
  have eq3262 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (k (M.op X1 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq689 X0 X1
       grind)
    | exact superpose eq689 eq35
    | (have j1 := eq689 X0 X1
       grind)
    | exact resolve eq35 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq689
  have eq3273 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (k (M.op X1 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3262 X0 X1
       have i₂ := eq1990 (M.op X0 X1)
       grind)
    | exact superpose eq1990 eq3262
    | (have j0 := eq3262 X0 X1
       grind)
    | exact resolve eq3262 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3262
  have eq3334 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) ∨ (k (k X1 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3273 X0 X1
       have i₂ := eq1990 X1
       grind)
    | exact superpose eq1990 eq3273
    | (have j0 := eq3273 X0 X1
       grind)
    | exact resolve eq3273 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq3566 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2700 eq127
    | exact resolve eq127 eq2700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq3578 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2700 eq2137
    | exact resolve eq2137 eq2700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137 eq2700
  have eq3600 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3578
  have eq3617 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3600
    | exact resolve eq3600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3600
  have eq3627 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3566
    | exact resolve eq3566 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq3635 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3036 eq3627
    | exact resolve eq3627 eq3036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3627
  have eq3937 : (M.op (M.op x y) (M.op x y)) = (M.op (k x x) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1376
       have i₂ := eq2824
       grind)
    | exact superpose eq2824 eq1376
    | exact resolve eq1376 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq3965 : (k (M.op x y) (M.op x y)) = (M.op (k x x) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3937
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq3937
    | exact resolve eq3937 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937
  have eq3977 : (M.op x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2949 eq3965
    | exact resolve eq3965 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3965
  have eq3981 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3977
       have i₂ := eq1372
       grind)
    | exact superpose eq1372 eq3977
    | exact resolve eq3977 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3977
  have eq3983 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2949 eq3981
    | exact resolve eq3981 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3981
  have eq4030 : (M.op (M.op x y) (M.op x y)) = (M.op x (k y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1376
       have i₂ := eq3635
       grind)
    | exact superpose eq3635 eq1376
    | exact resolve eq1376 eq3635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4031 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1377
       have i₂ := eq3635
       grind)
    | exact superpose eq3635 eq1377
    | exact resolve eq1377 eq3635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4058 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3036 eq4031
    | exact resolve eq4031 eq3036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036 eq4031
  have eq4059 : (k (M.op x y) (M.op x y)) = (M.op x (k y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4030
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq4030
    | exact resolve eq4030 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030
  have eq4062 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2492 eq4059
    | exact resolve eq4059 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2492 eq4059
  have eq4063 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4062
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4062
    | exact resolve eq4062 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4062
  have eq4065 : (M.op (M.op x y) (M.op x y)) = (M.op x (k y y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1376
       have i₂ := eq2949
       grind)
    | exact superpose eq2949 eq1376
    | exact resolve eq1376 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376 eq2949
  have eq4090 : (k (M.op x y) (M.op x y)) = (M.op x (k y y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4065
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq4065
    | exact resolve eq4065 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065
  have eq4092 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2486 eq4090
    | exact resolve eq4090 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486 eq4090
  have eq4093 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4092
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4092
    | exact resolve eq4092 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4092
  have eq4125 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3983 eq53
    | exact resolve eq53 eq3983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3983
  have eq4137 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq4125
    | exact resolve eq4125 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4125
  have eq4140 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4137
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4137
    | exact resolve eq4137 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq4148 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4058 eq603
    | exact resolve eq603 eq4058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq4058
  have eq4157 : (M.op (M.op x y) (M.op x y)) = (M.op x (k x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4148
       have i₂ := eq1372
       grind)
    | exact superpose eq1372 eq4148
    | exact resolve eq4148 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148
  have eq4163 : (k (M.op x y) (M.op x y)) = (M.op x (k x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4157
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq4157
    | exact resolve eq4157 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4157
  have eq4167 : (M.op x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3635 eq4163
    | exact resolve eq4163 eq3635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4163
  have eq4169 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4167
       have i₂ := eq1372
       grind)
    | exact superpose eq1372 eq4167
    | exact resolve eq4167 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372 eq4167
  have eq4170 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3635 eq4169
    | exact resolve eq4169 eq3635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3635 eq4169
  have eq4171 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4063 eq4170
    | exact resolve eq4170 eq4063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4170
  have eq4172 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4171
  have eq4174 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4172
       grind)
    | exact superpose eq4172 eq24
    | exact resolve eq24 eq4172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4179 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq155
       have i₂ := eq4172
       grind)
    | exact superpose eq4172 eq155
    | (have r₁ := eq155
       have r₂ := eq4172
       grind)
    | exact resolve eq155 eq4172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4184 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1009
       have i₂ := eq4172
       grind)
    | exact superpose eq4172 eq1009
    | exact resolve eq1009 eq4172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq4192 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq4179
  have eq4198 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4192
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq4192
    | exact resolve eq4192 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192
  have eq4203 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4174
    | exact resolve eq4174 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4174
  have eq4335 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4093 eq53
    | exact resolve eq53 eq4093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4352 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq4335
    | exact resolve eq4335 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4335
  have eq4355 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4140 eq4352
    | exact resolve eq4352 eq4140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4140 eq4352
  have eq4356 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4355
  have eq4372 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4356 eq2129
    | exact resolve eq2129 eq4356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129 eq4356
  have eq4378 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq4372
  have eq4744 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq628 X0 X0
       have i₂ := eq1990 (M.op X0 X0)
       grind)
    | exact superpose eq1990 eq628
    | exact resolve eq628 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4750 : (σ x) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq1190
       have i₂ := eq1990 (k sF2 sF2)
       grind)
    | exact superpose eq1990 eq1190
    | exact resolve eq1190 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4784 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4744 X0
       have i₂ := eq1990 X0
       grind)
    | exact superpose eq1990 eq4744
    | exact resolve eq4744 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4744
  have eq6999 : y = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1377
       have i₂ := eq3028
       grind)
    | exact superpose eq3028 eq1377
    | exact resolve eq1377 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377 eq3028
  have eq7042 : y = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4172 eq6999
    | exact resolve eq6999 eq4172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172 eq6999
  have eq7043 : y = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq7042
  have eq7072 : y = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq7043
       have i₂ := eq11 sF0 (k sF0 sF0)
       grind)
    | exact superpose eq11 eq7043
    | (have j1 := eq11 (M.op x y) (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq7043 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7076 : y = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (k (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7043 eq11
    | (have j0 := eq11 (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq11 eq7043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7078 : (M.op x y) = (M.op (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7043 eq16
    | exact resolve eq16 eq7043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7094 : (M.op x y) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7078
       have i₂ := eq1990 (k sF0 sF0)
       grind)
    | exact superpose eq1990 eq7078
    | exact resolve eq7078 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7078
  have eq7096 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ y = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7076
       have i₂ := eq1990 (k sF0 sF0)
       grind)
    | exact superpose eq1990 eq7076
    | exact resolve eq7076 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7076
  have eq7097 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ y = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq7072
       have i₂ := eq1990 (k sF0 sF0)
       grind)
    | exact superpose eq1990 eq7072
    | exact resolve eq7072 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7072
  have eq7103 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7094
       have i₂ := eq4784 sF0
       grind)
    | exact superpose eq4784 eq7094
    | exact resolve eq7094 eq4784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7094
  have eq7105 : y = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7096
       have i₂ := eq4784 sF0
       grind)
    | exact superpose eq4784 eq7096
    | exact resolve eq7096 eq4784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7096
  have eq7106 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq7097
       have i₂ := eq4784 sF0
       grind)
    | exact superpose eq4784 eq7097
    | exact resolve eq7097 eq4784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784 eq7097
  have eq7110 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq7105 eq7106
    | exact resolve eq7106 eq7105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7105 eq7106
  have eq7111 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7103 eq7110
    | exact resolve eq7110 eq7103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7103 eq7110
  have eq7112 : y = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq7111
  have eq7727 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4198 eq4184
    | exact resolve eq4184 eq4198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7754 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq7727
  have eq7767 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq7754
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq7754
    | exact resolve eq7754 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7754
  have eq7773 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq4198 eq7767
    | exact resolve eq7767 eq4198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4198 eq7767
  have eq7774 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq7773
  have eq7780 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7774 eq53
    | exact resolve eq53 eq7774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7783 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7780
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7780
    | exact resolve eq7780 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7780
  have eq7785 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4203 eq7783
    | exact resolve eq7783 eq4203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7783
  have eq7794 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7785 eq700
    | exact resolve eq700 eq7785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq7785
  have eq7810 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq841 eq7794
    | exact resolve eq7794 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7794
  have eq8142 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7810 eq174
    | exact resolve eq174 eq7810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq7810
  have eq8164 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq8142
    | exact resolve eq8142 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8142
  have eq8173 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3617 eq8164
    | exact resolve eq8164 eq3617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3617 eq8164
  have eq8224 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8173 eq4184
    | exact resolve eq4184 eq8173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4184
  have eq8254 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8224
  have eq8267 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8254
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq8254
    | exact resolve eq8254 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8254
  have eq8273 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8173 eq8267
    | exact resolve eq8267 eq8173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173 eq8267
  have eq8274 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8273
  have eq8277 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8274 eq27
    | exact resolve eq27 eq8274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8274
  have eq8300 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8277
       have r₂ := eq4203
       grind)
    | exact resolve eq8277 eq4203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8277
  have eq8304 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8300 eq27
    | exact resolve eq27 eq8300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8314 : (σ y) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8300 eq1179
    | exact resolve eq1179 eq8300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8315 : (k (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8300 eq1197
    | exact resolve eq1197 eq8300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq8322 : (k (σ x) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1174 eq8315
    | exact resolve eq8315 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8315
  have eq8330 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4203 eq8304
    | exact resolve eq8304 eq4203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4203 eq8304
  have eq8335 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq8330
  have eq8418 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq8314
       have i₂ := eq11 sF2 (k sF2 sF2)
       grind)
    | exact superpose eq11 eq8314
    | (have j1 := eq11 (σ x) (k (σ x) (σ x))
       grind)
    | exact resolve eq8314 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8425 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ (σ y) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8314 eq11
    | (have j0 := eq11 (k (σ x) (σ x)) (k (σ x) (σ x))
       grind)
    | exact resolve eq11 eq8314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8314
  have eq8446 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1190 eq8425
    | exact resolve eq8425 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8425
  have eq8448 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | exact superpose eq1190 eq8418
    | exact resolve eq8418 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8418
  have eq8457 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8446 eq8448
    | exact resolve eq8448 eq8446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8446 eq8448
  have eq8460 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8457
    | exact resolve eq8457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8457
  have eq8462 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8300 eq8460
    | exact resolve eq8460 eq8300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460
  have eq8463 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8462
       have r₂ := eq8335
       grind)
    | exact resolve eq8462 eq8335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8462
  have eq11082 : (σ y) = (k (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7112 eq49
    | exact resolve eq49 eq7112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq7112
  have eq11088 : (σ y) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53 eq11082
    | exact resolve eq11082 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq11082
  have eq11093 : (σ y) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq11088
    | exact resolve eq11088 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11088
  have eq11095 : (σ y) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11093
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11093
    | exact resolve eq11093 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11093
  have eq11096 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4093 eq11095
    | exact resolve eq11095 eq4093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4093 eq11095
  have eq11411 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11096 eq711
    | (have j0 := eq711 (σ x) (k (σ x) (σ x))
       grind)
    | exact resolve eq711 eq11096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11096
  have eq11419 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1190 eq11411
    | exact resolve eq11411 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11411
  have eq11421 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11419
    | exact resolve eq11419 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11419
  have eq11423 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1190 eq11421
    | exact resolve eq11421 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq11421
  have eq11425 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2128 eq11423
    | exact resolve eq11423 eq2128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2128 eq11423
  have eq11426 : (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11425
       have r₂ := eq4378
       grind)
    | exact resolve eq11425 eq4378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4378 eq11425
  have eq17154 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11426 eq628
    | exact resolve eq628 eq11426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11426
  have eq17172 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1185 eq17154
    | exact resolve eq17154 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17154
  have eq17173 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq17172
  have eq17220 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17173 eq163
    | exact resolve eq163 eq17173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq17173
  have eq17261 : x = (k x x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17220
    | exact resolve eq17220 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17220
  have eq17274 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4063 eq17261
    | exact resolve eq17261 eq4063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4063 eq17261
  have eq17275 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq17274
  have eq17307 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17275 eq7043
    | exact resolve eq7043 eq17275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7043
  have eq17338 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq17307
  have eq17351 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17338
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq17338
    | exact resolve eq17338 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17338
  have eq17358 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17275 eq17351
    | exact resolve eq17351 eq17275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17275 eq17351
  have eq17359 : y = (M.op x y) := by grind
  clear eq17358
  have eq17360 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq18
    | exact resolve eq18 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq17361 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq24
    | exact resolve eq24 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq17365 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq52
    | exact resolve eq52 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq17366 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq155
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq155
    | (have r₁ := eq155
       have r₂ := eq17359
       grind)
    | exact resolve eq155 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq17379 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq17366
  have eq17385 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq17379
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq17379
    | exact resolve eq17379 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17379
  have eq17393 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq17361 eq20
    | exact resolve eq20 eq17361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17427 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17361 eq319
    | exact resolve eq319 eq17361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq18699 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq17385 eq17365
    | exact resolve eq17365 eq17385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18706 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17385 eq784
    | (have j0 := eq784 (M.op x y) X0
       grind)
    | (have r₁ := eq784 (M.op x y) x
       have r₂ := eq17385
       grind)
    | exact resolve eq784 eq17385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18716 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq18706 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18706
  have eq18726 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20 eq18699
    | exact resolve eq18699 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18699
  have eq18736 : (σ y) = (k (σ y) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq17393 eq18726
    | exact resolve eq18726 eq17393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18726
  have eq18751 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq18736 eq843
    | exact resolve eq843 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq18791 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq18736 eq784
    | (have j0 := eq784 (σ y) X0
       grind)
    | (have r₁ := eq784 (σ y) x
       have r₂ := eq18736
       grind)
    | exact resolve eq784 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18802 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq18791 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18791
  have eq19163 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1990 (M.op X0 X1)
       have i₂ := eq593 X1 X0
       grind)
    | (have i₁ := eq1990 (M.op X0 X0)
       have i₂ := eq593 X0 X0
       grind)
    | exact superpose eq593 eq1990
    | exact resolve eq1990 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19208 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19163 X0 X1
       have i₂ := eq1990 X1
       grind)
    | exact superpose eq1990 eq19163
    | exact resolve eq19163 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19163
  have eq19291 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19208 X0 X1
       have i₂ := eq1990 X0
       grind)
    | exact superpose eq1990 eq19208
    | exact resolve eq19208 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19208
  have eq19589 : ∀ X0 : G, (M.op (k X0 (M.op x y)) (M.op (M.op x y) (M.op x y))) = X0 ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq18716 eq628
    | exact resolve eq628 eq18716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19593 : ∀ X0 : G, (k (M.op X0 (M.op (M.op x y) (M.op x y))) (M.op x y)) = X0 ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq18716 eq34
    | exact resolve eq34 eq18716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq19651 : ∀ X0 : G, (k (M.op X0 (k (M.op x y) (M.op x y))) (M.op x y)) = X0 ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq19593 X0
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq19593
    | exact resolve eq19593 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19593
  have eq19655 : ∀ X0 : G, (M.op (k X0 (M.op x y)) (k (M.op x y) (M.op x y))) = X0 ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq19589 X0
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq19589
    | exact resolve eq19589 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19589
  have eq19687 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17385 eq19651
    | exact resolve eq19651 eq17385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19651
  have eq19689 : ∀ X0 : G, (M.op (k X0 (M.op x y)) (M.op x y)) = X0 ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17385 eq19655
    | exact resolve eq19655 eq17385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19655
  have eq19913 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq18802 eq18751
    | exact resolve eq18751 eq18802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18751
  have eq19964 : (σ y) = (M.op (k y y) (k y (σ y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq18802 eq1014
    | exact resolve eq1014 eq18802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq19986 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq19913
  have eq19991 : (σ y) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (σ y))) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq19964
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq19964
    | exact resolve eq19964 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19964
  have eq20023 : (σ y) = (M.op (M.op x y) (k (M.op x y) (σ y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq17385 eq19991
    | exact resolve eq19991 eq17385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19991
  have eq20069 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq19986 eq17427
    | exact resolve eq17427 eq19986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17427
  have eq20074 : x = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq29 eq20069
    | exact resolve eq20069 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20069
  have eq20077 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq7774 eq20074
    | exact resolve eq20074 eq7774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7774 eq20074
  have eq20088 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20077 eq46
    | exact resolve eq46 eq20077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq20103 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20 eq20088
    | exact resolve eq20088 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20088
  have eq20109 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq17393 eq20103
    | exact resolve eq20103 eq17393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20103
  have eq20115 : x = (k x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19986 eq20109
    | exact resolve eq20109 eq19986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19986 eq20109
  have eq20375 : (σ y) = (k (k (M.op x y) (σ y)) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq18802 eq19687
    | exact resolve eq19687 eq18802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18802 eq19687
  have eq20381 : (σ y) = (k (k (M.op x y) (σ y)) (M.op x y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq20375
  have eq20390 : (σ x) = (k (k (M.op x y) (σ x)) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20115 eq20381
    | exact resolve eq20381 eq20115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20381
  have eq20409 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20077 eq19689
    | exact resolve eq19689 eq20077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19689 eq20077
  have eq20461 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (k x (M.op x y)) := by grind
  clear eq20409
  have eq20473 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq20461
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq20461
    | exact resolve eq20461 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20461
  have eq20479 : x = (k x (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17385 eq20473
    | exact resolve eq20473 eq17385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17385 eq20473
  have eq20487 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20479 eq17365
    | exact resolve eq17365 eq20479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20479
  have eq20494 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq20487
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20487
    | exact resolve eq20487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20487
  have eq20657 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (k (M.op x y) (σ y)) (k (M.op x y) (σ y)))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20023 eq593
    | exact resolve eq593 eq20023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq20023
  have eq20670 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op x y) (M.op x y)) (k (k (M.op x y) (σ y)) (k (M.op x y) (σ y)))) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq20657
       have i₂ := eq1990 (k sF0 sF3)
       grind)
    | exact superpose eq1990 eq20657
    | exact resolve eq20657 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20657
  have eq20682 : (M.op (σ y) (σ y)) = (M.op (k (M.op x y) (M.op x y)) (k (k (M.op x y) (σ y)) (k (M.op x y) (σ y)))) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq20670
       have i₂ := eq1990 sF0
       grind)
    | exact superpose eq1990 eq20670
    | exact resolve eq20670 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20670
  have eq20689 : (M.op (σ y) (σ y)) = (k (M.op (M.op x y) (k (M.op x y) (σ y))) (M.op (M.op x y) (k (M.op x y) (σ y)))) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq20682
       have i₂ := eq19291 sF0 (k sF0 sF3)
       grind)
    | exact superpose eq19291 eq20682
    | exact resolve eq20682 eq19291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20682
  have eq20696 : (k (σ y) (σ y)) = (k (M.op (M.op x y) (k (M.op x y) (σ y))) (M.op (M.op x y) (k (M.op x y) (σ y)))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq841 eq20689
    | exact resolve eq20689 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq20689
  have eq20701 : (k (σ y) (σ y)) = (k (k (k (M.op x y) (σ y)) (M.op x y)) (k (k (M.op x y) (σ y)) (M.op x y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq18716 eq20696
    | exact resolve eq20696 eq18716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18716 eq20696
  have eq20704 : (σ y) = (k (k (k (M.op x y) (σ y)) (M.op x y)) (k (k (M.op x y) (σ y)) (M.op x y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq18736 eq20701
    | exact resolve eq20701 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18736 eq20701
  have eq20705 : (σ x) = (k (k (k (M.op x y) (σ x)) (M.op x y)) (k (k (M.op x y) (σ x)) (M.op x y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20115 eq20704
    | exact resolve eq20704 eq20115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20704
  have eq20706 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20390 eq20705
    | exact resolve eq20705 eq20390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20390 eq20705
  have eq20713 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20706 eq1179
    | exact resolve eq1179 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20770 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20115 eq20713
    | exact resolve eq20713 eq20115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20115 eq20713
  have eq20789 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20770 eq1185
    | exact resolve eq1185 eq20770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185 eq20770
  have eq20807 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20706 eq20789
    | exact resolve eq20789 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20789
  have eq20812 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq1174 eq20807
    | exact resolve eq20807 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq20807
  have eq20815 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20706 eq20812
    | exact resolve eq20812 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20706 eq20812
  have eq20818 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8300 eq20815
    | exact resolve eq20815 eq8300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8300 eq20815
  have eq20859 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20818 eq17365
    | exact resolve eq17365 eq20818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17365 eq20818
  have eq20886 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq20859
    | exact resolve eq20859 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20859
  have eq20896 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17393 eq20886
    | exact resolve eq20886 eq17393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20886
  have eq20916 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20896 eq845
    | exact resolve eq845 eq20896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq20955 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20896 eq784
    | (have j0 := eq784 (σ y) X0
       grind)
    | (have r₁ := eq784 (σ y) x
       have r₂ := eq20896
       grind)
    | exact resolve eq784 eq20896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq20896
  have eq20966 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq20955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20955
  have eq20985 : ∀ X0 : G, (M.op (k X0 (σ y)) (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20966 eq20916
    | exact resolve eq20916 eq20966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20916 eq20966
  have eq22160 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20494 eq20985
    | exact resolve eq20985 eq20494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20494 eq20985
  have eq22226 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq22160
    | exact resolve eq22160 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq22160
  have eq22227 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22226
  have eq22244 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22227 eq14
    | exact resolve eq14 eq22227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22227
  have eq22262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22244
    | exact resolve eq22244 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22244
  have eq22265 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22262
       have r₂ := eq27
       grind)
    | exact resolve eq22262 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22262
  have eq22270 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq22265 eq27
    | exact resolve eq27 eq22265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq22280 : (σ y) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | exact superpose eq22265 eq1179
    | exact resolve eq1179 eq22265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq22265
  have eq22316 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq17393 eq22270
    | exact resolve eq22270 eq17393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17393 eq22270
  have eq29871 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1990 (M.op (M.op X0 X0) X1)
       have i₂ := eq594 X1 X0
       grind)
    | exact superpose eq594 eq1990
    | exact resolve eq1990 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq29891 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29871 X0 X1
       have i₂ := eq1990 X0
       grind)
    | exact superpose eq1990 eq29871
    | exact resolve eq29871 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29871
  have eq29958 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29891 X0 X1
       have i₂ := eq1990 X1
       grind)
    | exact superpose eq1990 eq29891
    | exact resolve eq29891 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990 eq29891
  have eq132246 : (k (σ x) (σ x)) = (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (σ x) (σ x))) ∨ (σ y) = (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (σ x) (σ x))) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8322 eq3334
    | (have j0 := eq3334 x y
       grind)
    | exact resolve eq3334 eq8322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334 eq8322
  have eq132311 : (k (σ x) (σ x)) = (k (M.op (k (σ x) (σ x)) (σ x)) (M.op (k (σ x) (σ x)) (σ x))) ∨ (σ y) = (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (σ x) (σ x))) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132246
       have i₂ := eq19291 (k sF2 sF2) sF2
       grind)
    | exact superpose eq19291 eq132246
    | exact resolve eq132246 eq19291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19291 eq132246
  have eq132452 : (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ y) = (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (σ x) (σ x))) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132311
       have i₂ := eq29958 sF2 sF2
       grind)
    | exact superpose eq29958 eq132311
    | exact resolve eq132311 eq29958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29958 eq132311
  have eq132561 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (σ x) (σ x))) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22280 eq132452
    | exact resolve eq132452 eq22280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22280 eq132452
  have eq132562 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq132561
  have eq132648 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4750 eq132562
    | exact resolve eq132562 eq4750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4750 eq132562
  have eq132714 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8463 eq132648
    | exact resolve eq132648 eq8463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8463 eq132648
  have eq132759 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq132714
       have r₂ := eq8335
       grind)
    | exact resolve eq132714 eq8335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8335 eq132714
  have eq133863 : (τ (σ y)) = (k x (τ (k (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq132759 eq102
    | exact resolve eq102 eq132759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq132759
  have eq133878 : (τ (σ y)) = (k x (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq109 eq133863
    | exact resolve eq133863 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq133863
  have eq133884 : y = (k x (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq133878
    | exact resolve eq133878 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq133878
  have eq133886 : (M.op x y) = (k x (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133884
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq133884
    | exact resolve eq133884 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17359 eq133884
  have eq133993 : x = (M.op (M.op (k x x) (k x x)) (M.op x y)) ∨ (k x x) = (M.op x (k x x)) ∨ (k x x) = (M.op (k x x) (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq711 x (k x x)
       have i₂ := eq133886
       grind)
    | exact superpose eq133886 eq711
    | (have j0 := eq711 x (k x x)
       grind)
    | exact resolve eq711 eq133886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq134000 : x = (M.op x (M.op x y)) ∨ (k x x) = (M.op x (k x x)) ∨ (k x x) = (M.op (k x x) (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133993
       have i₂ := eq1388
       grind)
    | exact superpose eq1388 eq133993
    | exact resolve eq133993 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133993
  have eq134009 : x = (M.op x y) ∨ (k x x) = (M.op x (k x x)) ∨ (k x x) = (M.op (k x x) (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17360 eq134000
    | exact resolve eq134000 eq17360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17360 eq134000
  have eq134010 : x = (M.op x y) ∨ (k x x) = (M.op x (k x x)) ∨ (k x x) = (M.op (k x x) (k x x)) := by grind
  clear eq134009
  have eq134018 : (k x x) = (M.op x (k x x)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq134010
       have i₂ := eq1388
       grind)
    | exact superpose eq1388 eq134010
    | exact resolve eq134010 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388 eq134010
  have eq134753 : (k x x) = (M.op (k x x) (M.op x x)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq628 x (k x x)
       have i₂ := eq134018
       grind)
    | exact superpose eq134018 eq628
    | exact resolve eq628 eq134018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq134018
  have eq134800 : x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq134753
       have i₂ := eq1383 x
       grind)
    | exact superpose eq1383 eq134753
    | exact resolve eq134753 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383 eq134753
  have eq134801 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq134800
  have eq134888 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133886
       have i₂ := eq134801
       grind)
    | exact superpose eq134801 eq133886
    | exact resolve eq133886 eq134801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133886
  have eq134950 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq134888
  have eq135172 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134801
       have i₂ := eq134950
       grind)
    | exact superpose eq134950 eq134801
    | exact resolve eq134801 eq134950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134801 eq134950
  have eq135255 : x = (M.op x y) := by grind
  clear eq135172
  have eq135297 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq135255
       grind)
    | exact superpose eq135255 eq22
    | exact resolve eq22 eq135255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq135255
  have eq135528 : (σ x) = (σ y) := by
    first
    | exact superpose eq135297 eq17361
    | exact resolve eq17361 eq135297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17361 eq135297
  have eq135868 : False := by grind
  exact eq135868

/-- `Equation1833`: `x = (x ◇ (x ◇ x)) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation1833 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1833 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1833.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq70 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq74 (σ X0)
       grind)
    | exact superpose eq74 eq15
    | exact resolve eq15 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq82
    | exact resolve eq82 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq82
  have eq107 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq110 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq107
    | exact resolve eq107 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq113 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq110
  have eq176 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq178 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq181 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq89 X1
       grind)
    | exact superpose eq89 eq176
    | (have j0 := eq176 X0 X1
       grind)
    | exact resolve eq176 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1490 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq178 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq178
    | exact resolve eq178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1548 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1490 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1490
    | (have j0 := eq1490 X0 X1
       grind)
    | exact resolve eq1490 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq3119 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181 x y
       grind)
    | exact superpose eq181 eq16
    | (have j1 := eq181 x y
       grind)
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq6089 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3119
       have i₂ := eq1548 x y
       grind)
    | exact superpose eq1548 eq3119
    | (have j1 := eq1548 x y
       grind)
    | (have r₁ := eq3119
       have r₂ := eq1548 x y
       grind)
    | (have r₁ := eq3119
       have r₂ := eq1548 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3119
       have r₂ := eq1548 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3119 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548 eq3119
  have eq6090 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq6089
  have eq6092 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6090
       grind)
    | exact superpose eq6090 eq16
    | exact resolve eq16 eq6090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6090
  have eq6093 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6092
       have r₂ := eq89 x
       grind)
    | exact resolve eq6092 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6092
  have eq6104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq113 y
       have i₂ := eq6093
       grind)
    | exact superpose eq6093 eq113
    | exact resolve eq113 eq6093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6093
  have eq6126 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq6104
       have r₂ := eq16
       grind)
    | exact resolve eq6104 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6104
  have eq6130 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6126
       grind)
    | exact superpose eq6126 eq10
    | exact resolve eq10 eq6126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6126
  have eq6187 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6130
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6130
    | exact resolve eq6130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6130
  have eq6190 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6187
       grind)
    | exact superpose eq6187 eq16
    | exact resolve eq16 eq6187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6187
  have eq6191 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq6190
       have r₂ := eq89 x
       grind)
    | exact resolve eq6190 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq6190
  have eq6204 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq6191
       grind)
    | exact superpose eq6191 eq10
    | exact resolve eq10 eq6191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191
  have eq6261 : x = (M.op y y) := by
    first
    | (have i₁ := eq6204
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6204
    | exact resolve eq6204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6204
  have eq6278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq113 y
       have i₂ := eq6261
       grind)
    | exact superpose eq6261 eq113
    | exact resolve eq113 eq6261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq6261
  have eq6299 : False := by grind
  exact eq6299

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq73
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq79
    | exact resolve eq79 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80
    | exact resolve eq80 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
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
  clear eq36
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq108
  have eq130 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq153 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq221 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq274 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq62
    | (have j0 := eq62 y x
       grind)
    | exact resolve eq62 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq62
    | (have j0 := eq62 (σ y) (σ x)
       grind)
    | exact resolve eq62 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq59 (M.op X0 X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq59
    | exact resolve eq59 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : y ≠ (M.op y y) ∨ (M.op x y) = (k (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq274 eq13
    | (have j0 := eq13 y y
       grind)
    | exact resolve eq13 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq441 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (M.op X0 X0) X0 X1 X2
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 y x X0 X1
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq478 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X2 (M.op X0 X1) X1
       have i₂ := eq62 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq62 eq58
    | exact resolve eq58 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq596 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq59 (σ X0)
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq59
    | (have j1 := eq69 X0 X0
       grind)
    | exact resolve eq59 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq609 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq596 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq1951 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq221 X0 sF4
       have i₂ := eq62 sF4 sF4
       grind)
    | exact superpose eq62 eq221
    | exact resolve eq221 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2944 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq454
    | (have j0 := eq454 (σ y) X0 (σ x)
       grind)
    | exact resolve eq454 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2966 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq454 X0 X0 X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq454
    | exact resolve eq454 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq2992 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2966 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2966
    | (have j0 := eq2966 y x
       grind)
    | exact resolve eq2966 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2994 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq2966
    | (have j0 := eq2966 (σ y) (σ x)
       grind)
    | exact resolve eq2966 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2966
  have eq3167 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq459 x X1 X0
       have i₂ := eq62 x x
       grind)
    | exact superpose eq62 eq459
    | exact resolve eq459 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq3242 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3167 sF0 sF0
       have i₂ := eq59 sF0
       grind)
    | exact superpose eq59 eq3167
    | exact resolve eq3167 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3345 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq609 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq609
    | (have j0 := eq609 X0
       have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq609 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq3364 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3345 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345
  have eq3410 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq450 (M.op y X0) X0
       have i₂ := eq62 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq62 eq450
    | exact resolve eq450 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq3549 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq457 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq59 (M.op X0 X1)
       grind)
    | exact superpose eq59 eq457
    | exact resolve eq457 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq457
  have eq3898 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq95 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95
    | (have j0 := eq95 y
       grind)
    | exact resolve eq95 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3914 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3898
  have eq3918 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3914
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq3914
    | exact resolve eq3914 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq3914
  have eq7139 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq62 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq62 eq441
    | exact resolve eq441 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq11388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11389 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq11388
    | exact resolve eq11388 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11388
  have eq11400 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq11389
       have r₂ := eq27
       grind)
    | exact resolve eq11389 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11389
  have eq11402 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq11400
    | exact resolve eq11400 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11400
  have eq11408 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq11402 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11402
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11402
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11402
       grind)
    | exact resolve eq12 eq11402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11402
  have eq11423 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq11408
  have eq11424 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq11423
       have r₂ := eq51
       grind)
    | exact resolve eq11423 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq11423
  have eq11425 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq11424
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq11424
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq11424
       have r₂ := eq13 y x
       grind)
    | exact resolve eq11424 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11424
  have eq11430 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq11425 eq55
    | exact resolve eq55 eq11425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq11431 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq11425 eq81
    | exact resolve eq81 eq11425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq11425
  have eq11443 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq11431
  have eq11452 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq11430
    | exact resolve eq11430 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11430
  have eq11457 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq11452
       have r₂ := eq50
       grind)
    | exact resolve eq11452 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11452
  have eq11471 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq11457
       grind)
    | exact superpose eq11457 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq11457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11457
  have eq11472 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq11471
  have eq11474 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11472
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11472
    | exact resolve eq11472 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11472
  have eq11485 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11474
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11474
    | exact resolve eq11474 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11474
  have eq11642 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq11443
       grind)
    | exact superpose eq11443 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11443
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11443
       grind)
    | exact resolve eq12 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11644 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq11443
       grind)
    | exact superpose eq11443 eq14
    | exact resolve eq14 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11657 : y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq11642
  have eq11658 : y = (M.op x y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq11657
       have r₂ := eq50
       grind)
    | exact resolve eq11657 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11657
  have eq11659 : x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq11658
       have r₂ := eq13 x y
       grind)
    | exact resolve eq11658 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11658
  have eq11661 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11659
       grind)
    | exact superpose eq11659 eq44
    | exact resolve eq44 eq11659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11659
  have eq11682 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11661
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11661
    | exact resolve eq11661 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11661
  have eq11821 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11682 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq11682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11682
  have eq11824 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq11821
    | exact resolve eq11821 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11821
  have eq11835 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq11824
    | exact resolve eq11824 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11824
  have eq11841 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq11485
       grind)
    | exact superpose eq11485 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11485
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11485
       grind)
    | exact resolve eq12 eq11485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11485
  have eq11856 : y = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11841
  have eq11857 : y = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11856
       have r₂ := eq50
       grind)
    | exact resolve eq11856 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq11856
  have eq11858 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq11857
       have r₂ := eq13 x y
       grind)
    | exact resolve eq11857 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11857
  have eq11968 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11858
       grind)
    | exact superpose eq11858 eq44
    | exact resolve eq44 eq11858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq11858
  have eq11990 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11968
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11968
    | exact resolve eq11968 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11968
  have eq12023 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11990 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq11990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11990
  have eq12024 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12023
    | exact resolve eq12023 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12023
  have eq12035 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12024
    | exact resolve eq12024 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12024
  have eq28381 : y = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11644 y
       have i₂ := eq11443
       grind)
    | exact superpose eq11443 eq11644
    | exact resolve eq11644 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11644
  have eq28413 : y = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq28381
  have eq29581 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 x) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq478 x (M.op y y) x
       have i₂ := eq28413
       grind)
    | exact superpose eq28413 eq478
    | exact resolve eq478 eq28413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq31053 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq3549 x x y
       have i₂ := eq11443
       grind)
    | exact superpose eq11443 eq3549
    | exact resolve eq3549 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31150 : ∀ X0 : G, (M.op x x) = (M.op (M.op x X0) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq3549 x X0 x
       have i₂ := eq31053 x
       grind)
    | exact superpose eq31053 eq3549
    | exact resolve eq3549 eq31053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31053
  have eq31356 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq31150 (M.op y y)
       have i₂ := eq28413
       grind)
    | exact superpose eq28413 eq31150
    | exact resolve eq31150 eq28413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28413 eq31150
  have eq31390 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq31356
  have eq31398 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11443
       have i₂ := eq31390
       grind)
    | exact superpose eq31390 eq11443
    | exact resolve eq11443 eq31390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31390
  have eq31431 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq31398
  have eq31470 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq31431
       grind)
    | exact superpose eq31431 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq31431
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq31431
       grind)
    | exact resolve eq13 eq31431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31431
  have eq31490 : x = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq31470
  have eq31536 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq605 x x
       have i₂ := eq31490
       grind)
    | exact superpose eq31490 eq605
    | (have j0 := eq605 x x
       grind)
    | exact resolve eq605 eq31490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31490
  have eq31539 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq31536
  have eq31540 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq31539
  have eq31551 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq31540
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31540
    | exact resolve eq31540 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31540
  have eq31610 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31551 eq1951
    | exact resolve eq1951 eq31551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951 eq31551
  have eq32082 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq31610 eq62
    | exact resolve eq62 eq31610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31610
  have eq33701 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq29581 y
       have i₂ := eq11443
       grind)
    | exact superpose eq11443 eq29581
    | exact resolve eq29581 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11443 eq29581
  have eq33742 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq33701
  have eq33754 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq33742
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33742
    | exact resolve eq33742 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33742
  have eq33760 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq33754
       grind)
    | exact superpose eq33754 eq114
    | exact resolve eq114 eq33754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq33754
  have eq33826 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq33760
  have eq33834 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq33826
    | exact resolve eq33826 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33826
  have eq34132 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3918 eq33834
    | exact resolve eq33834 eq3918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3918
  have eq78707 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq32082 eq3549
    | exact resolve eq3549 eq32082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32082
  have eq182906 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq34132 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq34132
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq34132
       grind)
    | exact resolve eq13 eq34132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182934 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq34132
  have eq182935 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq182906
  have eq227361 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq182935 eq33834
    | exact resolve eq33834 eq182935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33834 eq182935
  have eq227415 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq227361
  have eq227426 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq227415
       have r₂ := eq182934
       grind)
    | exact resolve eq227415 eq182934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182934 eq227415
  have eq227459 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq227426 eq2944
    | exact resolve eq2944 eq227426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944
  have eq227477 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq227426 eq278
    | exact resolve eq278 eq227426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq227493 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq227426 eq62
    | exact resolve eq62 eq227426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227510 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq227426 eq3549
    | exact resolve eq3549 eq227426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231783 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq227459 eq78707
    | exact resolve eq78707 eq227459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78707 eq227459
  have eq231838 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq231783
  have eq252303 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq227493 eq227510
    | exact resolve eq227510 eq227493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227493 eq227510
  have eq252377 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq252303 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252303
  have eq252426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11835 eq252377
    | exact resolve eq252377 eq11835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11835 eq252377
  have eq252541 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq252426
  have eq252566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq252541
    | exact resolve eq252541 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252541
  have eq252578 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq252566
       have r₂ := eq27
       grind)
    | exact resolve eq252566 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252566
  have eq252675 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq252578 eq231838
    | exact resolve eq231838 eq252578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231838 eq252578
  have eq252691 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq252675
  have eq252765 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq252691
    | exact resolve eq252691 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252691
  have eq253022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq252765 eq227477
    | exact resolve eq227477 eq252765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227477 eq252765
  have eq253090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq253022
  have eq253099 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq253090
       have r₂ := eq27
       grind)
    | exact resolve eq253090 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253090
  have eq253118 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq253099 eq2994
    | exact resolve eq2994 eq253099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2994 eq253099
  have eq253295 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq253118
    | exact resolve eq253118 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253118
  have eq253384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq253295 eq227426
    | exact resolve eq227426 eq253295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227426 eq253295
  have eq253476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq253384
  have eq253492 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq253476
       have r₂ := eq27
       grind)
    | exact resolve eq253476 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253476
  have eq253498 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq253492 eq28
    | exact resolve eq28 eq253492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq253492
  have eq253965 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq253498
    | exact resolve eq253498 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253498
  have eq254654 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq253965 eq20
    | exact resolve eq20 eq253965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254816 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq253965 eq3242
    | exact resolve eq3242 eq253965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq254866 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq255015 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq254654
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq254654
    | exact resolve eq254654 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254654
  have eq255086 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq255015 eq26
    | exact resolve eq26 eq255015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255108 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq255015 eq275
    | exact resolve eq275 eq255015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq259724 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3410 x
       have i₂ := eq254816
       grind)
    | exact superpose eq254816 eq3410
    | exact resolve eq3410 eq254816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410 eq254816
  have eq259828 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq259724
       have i₂ := eq62 x x
       grind)
    | exact superpose eq62 eq259724
    | exact resolve eq259724 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259724
  have eq264072 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq259828 eq14
    | exact resolve eq14 eq259828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259828
  have eq301062 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264072 eq7139
    | exact resolve eq7139 eq264072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7139 eq264072
  have eq301163 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq253965 eq301062
    | exact resolve eq301062 eq253965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301062
  have eq301325 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq301163
       have r₂ := eq254866
       grind)
    | exact resolve eq301163 eq254866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254866 eq301163
  have eq301328 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq301325
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq301325
    | exact resolve eq301325 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301325
  have eq301410 : y ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq287
       have i₂ := eq301328
       grind)
    | exact superpose eq301328 eq287
    | exact resolve eq287 eq301328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301489 : y ≠ (M.op x y) ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq301328
       grind)
    | exact superpose eq301328 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq301328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301328
  have eq301555 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq301489
       have r₂ := eq253965
       grind)
    | exact resolve eq301489 eq253965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301489
  have eq301566 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq301410
       have r₂ := eq253965
       grind)
    | exact resolve eq301410 eq253965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253965 eq301410
  have eq302241 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq605 y y
       have i₂ := eq301555
       grind)
    | exact superpose eq301555 eq605
    | (have j0 := eq605 y y
       grind)
    | exact resolve eq605 eq301555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301555
  have eq302244 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq302241
  have eq302245 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq302244
  have eq302276 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq302245
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq302245
    | exact resolve eq302245 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302245
  have eq302704 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq301566 eq605
    | (have j0 := eq605 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq605 eq301566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301566
  have eq302707 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq302704
  have eq302708 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq302707
  have eq302753 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq302708
    | exact resolve eq302708 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302708
  have eq307244 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq302276 eq3549
    | exact resolve eq3549 eq302276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3549
  have eq310872 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq302753 eq255108
    | exact resolve eq255108 eq302753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255108 eq302753
  have eq310950 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq310872
  have eq549421 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq302276 eq307244
    | exact resolve eq307244 eq302276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302276 eq307244
  have eq549580 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq549421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549421
  have eq549638 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12035 eq549580
    | exact resolve eq549580 eq12035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12035 eq549580
  have eq549801 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq549638
  have eq549825 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq549801
    | exact resolve eq549801 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549801
  have eq549826 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq549825
  have eq549836 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq549826 eq27
    | exact resolve eq27 eq549826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549826
  have eq550110 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq549836
       have r₂ := eq255015
       grind)
    | exact resolve eq549836 eq255015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255015 eq549836
  have eq550267 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq550110 eq310950
    | exact resolve eq310950 eq550110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310950 eq550110
  have eq550331 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq550267
  have eq550394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq550331 eq255086
    | exact resolve eq255086 eq550331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255086 eq550331
  have eq550501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq550394
  have eq550509 : x = (M.op x y) := by
    first
    | (have r₁ := eq550501
       have r₂ := eq27
       grind)
    | exact resolve eq550501 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550501
  have eq551931 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq550509 eq20
    | exact resolve eq20 eq550509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq552096 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq550509 eq2992
    | exact resolve eq2992 eq550509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq552281 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq552096
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq552096
    | exact resolve eq552096 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq552096
  have eq552425 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq551931
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq551931
    | exact resolve eq551931 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551931
  have eq552426 : x = (M.op y y) := by
    first
    | exact superpose eq550509 eq552281
    | exact resolve eq552281 eq550509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552281
  have eq552427 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq552425 eq26
    | exact resolve eq26 eq552425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552995 : x ≠ y ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq287
       have i₂ := eq552426
       grind)
    | exact superpose eq552426 eq287
    | exact resolve eq287 eq552426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq553120 : y = (M.op x x) := by
    first
    | (have i₁ := eq62 y y
       have i₂ := eq552426
       grind)
    | exact superpose eq552426 eq62
    | exact resolve eq62 eq552426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq552426
  have eq553198 : x ≠ y ∨ x = (k x x) := by
    first
    | exact superpose eq550509 eq552995
    | exact resolve eq552995 eq550509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552995
  have eq554710 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq553120
       grind)
    | exact superpose eq553120 eq78
    | exact resolve eq78 eq553120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq554808 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq3364 x
       have i₂ := eq553120
       grind)
    | exact superpose eq553120 eq3364
    | (have j0 := eq3364 x
       grind)
    | exact resolve eq3364 eq553120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364 eq553120
  have eq554892 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq554808
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq554808
    | exact resolve eq554808 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554808
  have eq554908 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq552425 eq554710
    | exact resolve eq554710 eq552425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554710
  have eq554919 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq554892
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq554892
    | exact resolve eq554892 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554892
  have eq554926 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq554908
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq554908
    | exact resolve eq554908 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554908
  have eq554930 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq554919
    | exact resolve eq554919 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq554919
  have eq554936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq552425 eq554930
    | exact resolve eq554930 eq552425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554930
  have eq554942 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq554936
       have r₂ := eq27
       grind)
    | exact resolve eq554936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554936
  have eq554944 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq554942
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq554942
    | exact resolve eq554942 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554942
  have eq554945 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq552425 eq554944
    | exact resolve eq554944 eq552425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554944
  have eq574380 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq554926 eq153
    | exact resolve eq153 eq554926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554926
  have eq574471 : (τ (σ y)) = (k x x) ∨ x = y := by
    first
    | exact superpose eq550509 eq574380
    | exact resolve eq574380 eq550509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574380
  have eq574483 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq29 eq574471
    | exact resolve eq574471 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq574471
  have eq577317 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq554945 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq554945
       grind)
    | exact resolve eq13 eq554945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554945
  have eq577371 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq577317
  have eq582544 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq577371 eq153
    | exact resolve eq153 eq577371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq577371
  have eq582659 : (τ (σ (M.op x y))) = (k x x) ∨ x = y := by
    first
    | exact superpose eq550509 eq582544
    | exact resolve eq582544 eq550509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582544
  have eq582669 : (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq30 eq582659
    | exact resolve eq582659 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq582659
  have eq582677 : x = (k x x) ∨ x = y := by
    first
    | exact superpose eq550509 eq582669
    | exact resolve eq582669 eq550509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550509 eq582669
  have eq582681 : x = (k x x) := by
    first
    | (have r₁ := eq582677
       have r₂ := eq553198
       grind)
    | exact resolve eq582677 eq553198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553198 eq582677
  have eq582705 : x = y ∨ x = y := by
    first
    | (have i₁ := eq574483
       have i₂ := eq582681
       grind)
    | exact superpose eq582681 eq574483
    | exact resolve eq574483 eq582681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574483
  have eq582760 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq605 x x
       have i₂ := eq582681
       grind)
    | exact superpose eq582681 eq605
    | (have j0 := eq605 x x
       grind)
    | exact resolve eq605 eq582681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq582681
  have eq582776 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq582760
  have eq582777 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq582776
  have eq582795 : x = y := by grind
  clear eq582705
  have eq582804 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq582777
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq582777
    | exact resolve eq582777 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582777
  have eq582870 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq552425 eq582804
    | exact resolve eq582804 eq552425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582804
  have eq583053 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq582795
       grind)
    | exact superpose eq582795 eq24
    | exact resolve eq24 eq582795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq582795
  have eq584023 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq583053
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq583053
    | exact resolve eq583053 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq583053
  have eq584194 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq552425 eq584023
    | exact resolve eq584023 eq552425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552425 eq584023
  have eq586451 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq584194 eq552427
    | exact resolve eq552427 eq584194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552427 eq584194
  have eq603311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq582870 eq586451
    | exact resolve eq586451 eq582870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582870 eq586451
  have eq603312 : False := by grind
  exact eq603312

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,Y) else if m(Y,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pyy_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq94 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq92
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq103
  have eq247 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 X0) X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3320 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq379 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq379
    | exact resolve eq379 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq3916 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq382 X0 X0 X2 X3 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq382
    | exact resolve eq382 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq382
  have eq4389 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq94 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq94
    | (have j0 := eq94 y
       grind)
    | exact resolve eq94 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq94
  have eq4402 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4389
  have eq4405 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4402
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq4402
    | exact resolve eq4402 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4402
  have eq4426 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4405
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4405 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4405
  have eq4460 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4426 eq108
    | exact resolve eq108 eq4426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq13303 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4426 eq109
    | exact resolve eq109 eq4426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq18292 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3916 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq3916
    | exact resolve eq3916 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq3916
  have eq19758 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq13303
       grind)
    | exact superpose eq13303 eq16
    | exact resolve eq16 eq13303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13303
  have eq19826 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4460 eq19758
    | exact resolve eq19758 eq4460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19758
  have eq19832 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq19826
       have r₂ := eq13 y y
       grind)
    | exact resolve eq19826 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19826
  have eq19833 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19832
       grind)
    | exact superpose eq19832 eq92
    | exact resolve eq92 eq19832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq19869 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq4426 eq19833
    | exact resolve eq19833 eq4426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4426 eq19833
  have eq28400 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq28400
    | exact resolve eq28400 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28400
  have eq28412 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq28401
       have r₂ := eq28
       grind)
    | exact resolve eq28401 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28401
  have eq28420 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28412 eq4460
    | exact resolve eq4460 eq28412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4460 eq28412
  have eq28487 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq28420
       have i₂ := eq19832
       grind)
    | exact superpose eq19832 eq28420
    | exact resolve eq28420 eq19832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19832 eq28420
  have eq28497 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq28487
    | exact resolve eq28487 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28487
  have eq28498 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq28497
  have eq28516 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28498 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq28498
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq28498
       grind)
    | exact resolve eq13 eq28498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28532 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28498 eq18292
    | exact resolve eq18292 eq28498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28498
  have eq28534 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq28516
  have eq28535 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq28532
    | exact resolve eq28532 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28532
  have eq30490 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28534 eq86
    | exact resolve eq86 eq28534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq28534
  have eq30502 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq30490
  have eq31405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30502 eq28535
    | exact resolve eq28535 eq30502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28535 eq30502
  have eq31450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq31405
  have eq31460 : x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq31450
       have r₂ := eq28
       grind)
    | exact resolve eq31450 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31450
  have eq31493 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19869
       have i₂ := eq31460
       grind)
    | exact superpose eq31460 eq19869
    | exact resolve eq19869 eq31460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31515 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq247 y x
       have i₂ := eq31460
       grind)
    | exact superpose eq31460 eq247
    | exact resolve eq247 eq31460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31460
  have eq31559 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq31493
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31493
    | exact resolve eq31493 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq31493
  have eq32937 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq31559 eq247
    | exact resolve eq247 eq31559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq31559
  have eq58642 : (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3320 y (M.op x x)
       have i₂ := eq31515 x
       grind)
    | exact superpose eq31515 eq3320
    | exact resolve eq3320 eq31515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31515
  have eq58660 : (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq58642
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58642
    | exact resolve eq58642 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58642
  have eq58678 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19869
       have i₂ := eq58660
       grind)
    | exact superpose eq58660 eq19869
    | exact resolve eq19869 eq58660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58660
  have eq58764 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq58678
    | exact resolve eq58678 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58678
  have eq75064 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq32937 eq3320
    | exact resolve eq3320 eq32937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320 eq32937
  have eq75084 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq75064
    | exact resolve eq75064 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75064
  have eq75436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq75084 eq58764
    | exact resolve eq58764 eq75084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58764 eq75084
  have eq75494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq75436
  have eq75524 : x = (M.op y x) := by
    first
    | (have r₁ := eq75494
       have r₂ := eq28
       grind)
    | exact resolve eq75494 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75494
  have eq75568 : x ≠ x ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq75524
       grind)
    | exact superpose eq75524 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq75524
       grind)
    | exact resolve eq13 eq75524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75593 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18292 y x
       have i₂ := eq75524
       grind)
    | exact superpose eq75524 eq18292
    | exact resolve eq18292 eq75524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75524
  have eq75595 : (k x y) = (M.op y y) := by grind
  clear eq75568
  have eq75596 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq75593
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75593
    | exact resolve eq75593 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq75593
  have eq75935 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19869
       have i₂ := eq75596
       grind)
    | exact superpose eq75596 eq19869
    | exact resolve eq19869 eq75596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19869
  have eq76020 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq75935
    | exact resolve eq75935 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75935
  have eq76622 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq76020 eq250
    | exact resolve eq250 eq76020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq79701 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq75595
       have i₂ := eq75596
       grind)
    | exact superpose eq75596 eq75595
    | exact resolve eq75595 eq75596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75595 eq75596
  have eq80260 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq79701
       grind)
    | exact superpose eq79701 eq45
    | exact resolve eq45 eq79701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq79701
  have eq80305 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq80260
    | exact resolve eq80260 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq80260
  have eq80372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq80305 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80305
  have eq80373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq80372
    | exact resolve eq80372 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80372
  have eq80385 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq80373
       have r₂ := eq28
       grind)
    | exact resolve eq80373 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80373
  have eq80389 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq76020 eq80385
    | exact resolve eq80385 eq76020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80385
  have eq81552 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq80389 eq18292
    | exact resolve eq18292 eq80389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18292 eq80389
  have eq81555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq76020 eq81552
    | exact resolve eq81552 eq76020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76020 eq81552
  have eq81570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq81555
    | exact resolve eq81555 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81555
  have eq81578 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq81570
       have r₂ := eq28
       grind)
    | exact resolve eq81570 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81570
  have eq81583 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq81578 eq27
    | exact resolve eq27 eq81578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq81578
  have eq81809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76622 eq81583
    | exact resolve eq81583 eq76622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76622 eq81583
  have eq81877 : False := by grind
  exact eq81877

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq13
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq53 X0
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq68 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq64 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq70 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq77 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ x = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq76
    | exact resolve eq76 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq79
    | exact resolve eq79 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80
    | exact resolve eq80 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
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
  have eq101 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq102 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
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
  have eq112 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq101
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq112
  have eq127 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
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
  have eq243 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq279 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ y) (σ x)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq68
    | exact resolve eq68 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq38
    | exact resolve eq38 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq323 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq306 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq306
    | exact resolve eq306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq448 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0) X0 X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y x X0 X1
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    by_contra hcon
    push Not at hcon
    have f464_11 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
      intro X0 X1 X2 X3
      grind
    have f464_17 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
      intro X0 X1 X2
      grind
    have f464_20 : (M.op X1 X0) ≠ (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by grind
    have f464_69 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
      intro X0 X1 X2 X3 X4
      first
      | (have i₁ := f464_17 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
         have i₂ := f464_11 X1 X4 X0 X2
         grind)
      | exact superpose f464_11 f464_17
      | exact resolve f464_17 f464_11
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f464_157 : (M.op X1 X0) ≠ (M.op X1 X0) := by
      first
      | (have i₁ := f464_20
         have i₂ := f464_69 X2 X0 X3 X4 X1
         grind)
      | exact superpose f464_69 f464_20
      | (have r₁ := f464_20
         have r₂ := f464_69 X2 X0 X3 X4 X1
         grind)
      | exact resolve f464_20 f464_69
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f464_169 : False := by grind
    exact f464_169
  have eq466 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq52
  have eq587 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0)
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq53
    | (have j1 := eq69 X0 X0
       grind)
    | exact resolve eq53 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq598 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq601 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq587 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq3492 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X0 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq461
    | exact resolve eq461 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq3526 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3492 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3492
    | (have j0 := eq3492 y x
       grind)
    | exact resolve eq3492 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3528 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq3492
    | (have j0 := eq3492 (σ y) (σ x)
       grind)
    | exact resolve eq3492 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3589 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3528 eq14
    | exact resolve eq14 eq3528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3672 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq598 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq598
    | (have j0 := eq598 (σ X0)
       grind)
    | exact resolve eq598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq3715 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq466 x X1 X0
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq466
    | exact resolve eq466 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq3779 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3715 sF0 sF0
       have i₂ := eq53 sF0
       grind)
    | exact superpose eq53 eq3715
    | exact resolve eq3715 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3715
  have eq3808 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3779 eq14
    | exact resolve eq14 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3904 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq601 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq601
    | (have j0 := eq601 (τ X0)
       grind)
    | exact resolve eq601 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq3929 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3904 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3904
    | (have j0 := eq3904 X0
       grind)
    | exact resolve eq3904 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904
  have eq3940 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3929 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3929
    | (have j0 := eq3929 X0
       grind)
    | exact resolve eq3929 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3929
  have eq3983 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq457 (M.op y X0) X0
       have i₂ := eq55 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq55 eq457
    | exact resolve eq457 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq4048 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3589 sF3
       have i₂ := eq53 sF3
       grind)
    | exact superpose eq53 eq3589
    | exact resolve eq3589 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589
  have eq4086 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq4048 eq14
    | exact resolve eq14 eq4048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4048
  have eq4164 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq464 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq53 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq464
    | exact resolve eq464 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq4271 : (M.op x y) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq3808 x
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq3808
    | exact resolve eq3808 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq4382 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq70
    | (have j0 := eq70 x
       grind)
    | exact resolve eq70 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq4401 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4382
  have eq4406 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4401
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4401
    | exact resolve eq4401 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4401
  have eq4421 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4406
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq4406 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4406
  have eq4425 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4421 eq49
    | exact resolve eq49 eq4421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq4421
  have eq4568 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq103
    | (have j0 := eq103 y
       grind)
    | exact resolve eq103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq4587 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4568
  have eq4591 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4587
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq4587
    | exact resolve eq4587 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq4587
  have eq4613 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4591
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4591 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4591
  have eq4786 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq128
    | (have j0 := eq128 (M.op x y)
       grind)
    | exact resolve eq128 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq4803 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq4786
  have eq4806 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq127 eq4803
    | exact resolve eq4803 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq4835 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq4806
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4806 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4806
  have eq7526 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq55 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq55 eq448
    | exact resolve eq448 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq16217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16217
    | exact resolve eq16217 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16217
  have eq16236 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq16225
       have r₂ := eq27
       grind)
    | exact resolve eq16225 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16225
  have eq16238 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16236
    | exact resolve eq16236 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16236
  have eq16247 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16238 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq16238
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq16238
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16238
       grind)
    | exact resolve eq13 eq16238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16238
  have eq16267 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq16247
  have eq16276 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16267 eq81
    | exact resolve eq81 eq16267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16267
  have eq16291 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16276
  have eq16475 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3492 x y
       have i₂ := eq16291
       grind)
    | exact superpose eq16291 eq3492
    | exact resolve eq3492 eq16291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17078 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16291
       have i₂ := eq16475
       grind)
    | exact superpose eq16475 eq16291
    | exact resolve eq16291 eq16475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16291 eq16475
  have eq17106 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17078
  have eq17112 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4613 eq118
    | exact resolve eq118 eq4613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq4613
  have eq17123 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq17106
       grind)
    | exact superpose eq17106 eq53
    | exact resolve eq53 eq17106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17106
  have eq17154 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17123
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17123
    | exact resolve eq17123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17123
  have eq17155 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq17154
  have eq17171 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17155 eq3528
    | exact resolve eq3528 eq17155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528
  have eq17183 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17171
    | exact resolve eq17171 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17171
  have eq17359 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17183 eq279
    | exact resolve eq279 eq17183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17373 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17183 eq68
    | exact resolve eq68 eq17183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17183
  have eq17629 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17155 eq17359
    | exact resolve eq17359 eq17155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17359
  have eq17673 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq17629
  have eq17716 : (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17155 eq17373
    | exact resolve eq17373 eq17155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17155 eq17373
  have eq17726 : (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq17716
  have eq18313 : (τ (σ y)) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17673 eq4425
    | exact resolve eq4425 eq17673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4425 eq17673
  have eq18360 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq18313
    | exact resolve eq18313 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18313
  have eq18397 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17726 eq81
    | exact resolve eq81 eq17726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq17726
  have eq18412 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18397
  have eq18493 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3940 x
       have i₂ := eq18360
       grind)
    | exact superpose eq18360 eq3940
    | (have j0 := eq3940 x
       grind)
    | exact resolve eq3940 eq18360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3940
  have eq18522 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18493
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18493
    | exact resolve eq18493 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18493
  have eq18523 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18522
  have eq18598 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3492 x y
       have i₂ := eq18412
       grind)
    | exact superpose eq18412 eq3492
    | exact resolve eq3492 eq18412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18786 : x = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq68 x
       have i₂ := eq18523
       grind)
    | exact superpose eq18523 eq68
    | exact resolve eq68 eq18523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq18523
  have eq18834 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18360
       have i₂ := eq18786
       grind)
    | exact superpose eq18786 eq18360
    | exact resolve eq18360 eq18786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18360 eq18786
  have eq18863 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18834
  have eq18893 : y = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18863 eq29
    | exact resolve eq29 eq18863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18863
  have eq19018 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq18893
    | exact resolve eq18893 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18893
  have eq26095 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18412
       have i₂ := eq18598
       grind)
    | exact superpose eq18598 eq18412
    | exact resolve eq18412 eq18598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18412 eq18598
  have eq26132 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq26095
  have eq26155 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq26132
       grind)
    | exact superpose eq26132 eq53
    | exact resolve eq53 eq26132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26132
  have eq26192 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26155
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26155
    | exact resolve eq26155 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26155
  have eq26193 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq26192
  have eq26196 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26193 eq26
    | exact resolve eq26 eq26193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26197 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26193 eq29
    | exact resolve eq29 eq26193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26198 : ∀ X0 : G, (σ (k y X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26193 eq36
    | exact resolve eq36 eq26193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq26199 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26193 eq40
    | exact resolve eq40 eq26193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq26216 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26193 eq279
    | exact resolve eq279 eq26193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq26255 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26193 eq4086
    | exact resolve eq4086 eq26193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086
  have eq26326 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq26199
    | exact resolve eq26199 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26199
  have eq26327 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37 eq26198
    | exact resolve eq26198 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq26198
  have eq26328 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq26197
    | exact resolve eq26197 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26197
  have eq26432 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26328 eq3779
    | exact resolve eq3779 eq26328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26435 : y = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26328 eq4271
    | exact resolve eq4271 eq26328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4271
  have eq26439 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq26328
  have eq28312 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3983 x
       have i₂ := eq26432
       grind)
    | exact superpose eq26432 eq3983
    | exact resolve eq3983 eq26432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3983 eq26432
  have eq28353 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28312
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq28312
    | exact resolve eq28312 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28312
  have eq30984 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq19018 eq28353
    | exact resolve eq28353 eq19018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28353
  have eq31029 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq30984
  have eq31034 : x = (M.op y (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31029
       have r₂ := eq26439
       grind)
    | exact resolve eq31029 eq26439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31029
  have eq32708 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 (M.op x x)
       have i₂ := eq31034
       grind)
    | exact superpose eq31034 eq14
    | exact resolve eq14 eq31034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31034
  have eq34699 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26326 eq34
    | exact resolve eq34 eq26326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34854 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq34699
    | (have j0 := eq34699 X0
       grind)
    | exact resolve eq34699 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34699
  have eq34899 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34854 X0
       have i₂ := eq34 X0 y
       grind)
    | exact superpose eq34 eq34854
    | exact resolve eq34854 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34854
  have eq34930 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34899 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34899
    | (have j0 := eq34899 X0
       grind)
    | exact resolve eq34899 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34899
  have eq35543 : (σ y) = (k (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34930 eq323
    | exact resolve eq323 eq34930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq34930
  have eq35638 : (σ y) = (σ (k (M.op (τ (σ y)) (τ (σ y))) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41 eq35543
    | exact resolve eq35543 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq35543
  have eq35691 : (σ y) = (σ (k (M.op y y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq35638
    | exact resolve eq35638 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35638
  have eq36768 : ∀ X0 : G, (k (M.op x y) X0) = (τ (σ (k y X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26327 eq16
    | exact resolve eq16 eq26327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26327
  have eq36890 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq36768 X0
       have i₂ := eq16 (k y X0)
       grind)
    | exact superpose eq16 eq36768
    | exact resolve eq36768 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36768
  have eq37020 : ∀ X0 : G, (k (τ (M.op x y)) X0) = (τ (k y (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36890 eq243
    | exact resolve eq243 eq36890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36890
  have eq37163 : ∀ X0 : G, (k (τ (M.op x y)) X0) = (k (τ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq37020 X0
       have i₂ := eq243 y X0
       grind)
    | exact superpose eq243 eq37020
    | exact resolve eq37020 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq37020
  have eq39948 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X1) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq26255 eq4164
    | exact resolve eq4164 eq26255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4164 eq26255
  have eq47356 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq3779 eq77
    | exact resolve eq77 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq3779
  have eq150971 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7526 x (M.op y y)
       have i₂ := eq32708 x
       grind)
    | exact superpose eq32708 eq7526
    | exact resolve eq7526 eq32708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7526 eq32708
  have eq151185 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq150971
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq150971
    | exact resolve eq150971 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150971
  have eq151200 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26435
       have i₂ := eq151185
       grind)
    | exact superpose eq151185 eq26435
    | exact resolve eq26435 eq151185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26435
  have eq151202 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35691
       have i₂ := eq151185
       grind)
    | exact superpose eq151185 eq35691
    | exact resolve eq35691 eq151185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35691
  have eq151234 : (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq282 y
       have i₂ := eq151185
       grind)
    | exact superpose eq151185 eq282
    | exact resolve eq282 eq151185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq151185
  have eq151296 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq151202
  have eq151298 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq151200
  have eq151320 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq151296
    | exact resolve eq151296 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq151296
  have eq151328 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4835 eq151320
    | exact resolve eq151320 eq4835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151320
  have eq151671 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq151234 eq102
    | exact resolve eq102 eq151234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151234
  have eq151773 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq151671
    | exact resolve eq151671 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151671
  have eq152018 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq151298 eq47356
    | exact resolve eq47356 eq151298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47356 eq151298
  have eq152065 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq152018
       have r₂ := eq26439
       grind)
    | exact resolve eq152018 eq26439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152018
  have eq152068 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq152065
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq152065
    | exact resolve eq152065 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152065
  have eq152437 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq151328 eq39948
    | exact resolve eq39948 eq151328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39948 eq151328
  have eq152519 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq152437 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152437
  have eq157535 : (σ (σ (τ (M.op x y)))) ≠ (σ (σ (k (τ y) (τ (M.op x y))))) ∨ (σ (σ (τ (M.op x y)))) = (M.op (σ (σ (τ (M.op x y)))) (σ (σ (τ (M.op x y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37163 eq3672
    | (have j0 := eq3672 (τ (M.op x y))
       grind)
    | exact resolve eq3672 eq37163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672 eq37163
  have eq157621 : (σ (σ (τ (M.op x y)))) ≠ (σ (k y (σ (τ (M.op x y))))) ∨ (σ (σ (τ (M.op x y)))) = (M.op (σ (σ (τ (M.op x y)))) (σ (σ (τ (M.op x y))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq157535
       have i₂ := eq34 y (τ sF0)
       grind)
    | exact superpose eq34 eq157535
    | exact resolve eq157535 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq157535
  have eq157648 : (σ (M.op x y)) ≠ (σ (k y (M.op x y))) ∨ (σ (σ (τ (M.op x y)))) = (M.op (σ (σ (τ (M.op x y)))) (σ (σ (τ (M.op x y))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq157621
       have i₂ := eq15 sF0
       grind)
    | exact superpose eq15 eq157621
    | exact resolve eq157621 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157621
  have eq157665 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (σ (τ (M.op x y)))) = (M.op (σ (σ (τ (M.op x y)))) (σ (σ (τ (M.op x y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102 eq157648
    | exact resolve eq157648 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157648
  have eq157672 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (σ (τ (M.op x y)))) = (M.op (σ (σ (τ (M.op x y)))) (σ (σ (τ (M.op x y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq157665
    | exact resolve eq157665 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157665
  have eq157676 : (σ (σ (τ (M.op x y)))) = (M.op (σ (σ (τ (M.op x y)))) (σ (σ (τ (M.op x y))))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq157672
       have r₂ := eq151773
       grind)
    | exact resolve eq157672 eq151773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151773 eq157672
  have eq157680 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq157676
       have i₂ := eq15 sF0
       grind)
    | exact superpose eq15 eq157676
    | exact resolve eq157676 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157676
  have eq157682 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq157680
    | exact resolve eq157680 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157680
  have eq157691 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq157682 eq26216
    | exact resolve eq26216 eq157682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26216 eq157682
  have eq157807 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq157691
  have eq489112 : (τ (σ y)) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq152068 eq63
    | exact resolve eq63 eq152068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152068
  have eq489168 : (M.op x y) = (M.op x x) ∨ y = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq489112
    | exact resolve eq489112 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq489112
  have eq505072 : y = (k x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq489168
       grind)
    | exact superpose eq489168 eq53
    | exact resolve eq53 eq489168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq489168
  have eq537763 : y = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq19018 eq505072
    | exact resolve eq505072 eq19018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19018 eq505072
  have eq537869 : y = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq537763
  have eq537934 : y = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq537869
       have r₂ := eq26439
       grind)
    | exact resolve eq537869 eq26439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26439 eq537869
  have eq537985 : x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq537934
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq537934
    | exact resolve eq537934 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537934
  have eq537986 : y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq537985
  have eq538107 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq537986
       grind)
    | exact superpose eq537986 eq44
    | exact resolve eq44 eq537986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537986
  have eq538240 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq538107
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq538107
    | exact resolve eq538107 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538107
  have eq538722 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26193 eq538240
    | exact resolve eq538240 eq26193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26193 eq538240
  have eq538822 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq538722
  have eq540712 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq538822 eq63
    | exact resolve eq63 eq538822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq538822
  have eq540775 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq540712
    | exact resolve eq540712 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq540712
  have eq542925 : (σ (M.op x y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq540775 eq26326
    | exact resolve eq26326 eq540775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26326 eq540775
  have eq542967 : (σ (M.op x y)) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq542925
  have eq543014 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq542967
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq542967
    | exact resolve eq542967 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq542967
  have eq543068 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq543014
    | exact resolve eq543014 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543014
  have eq543598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq543068 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq543068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543068
  have eq543657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq543598
    | exact resolve eq543598 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543598
  have eq543678 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq543657
       have r₂ := eq27
       grind)
    | exact resolve eq543657 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543657
  have eq543681 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq543678
    | exact resolve eq543678 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543678
  have eq548353 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq543681 eq55
    | exact resolve eq55 eq543681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq543681
  have eq755344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq548353 eq152519
    | exact resolve eq152519 eq548353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152519 eq548353
  have eq755511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq755344
  have eq755538 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq755511
    | exact resolve eq755511 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755511
  have eq755542 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq755538
       have r₂ := eq27
       grind)
    | exact resolve eq755538 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755538
  have eq755698 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq755542 eq157807
    | exact resolve eq157807 eq755542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157807 eq755542
  have eq755713 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq755698
  have eq755830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq755713 eq26196
    | exact resolve eq26196 eq755713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26196 eq755713
  have eq755962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq755830
  have eq755977 : x = (M.op x y) := by
    first
    | (have r₁ := eq755962
       have r₂ := eq27
       grind)
    | exact resolve eq755962 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755962
  have eq755984 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq755977 eq20
    | exact resolve eq20 eq755977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq755988 : x ≠ x ∨ x = (k y x) := by
    first
    | exact superpose eq755977 eq66
    | (have r₁ := eq66
       have r₂ := eq755977
       grind)
    | exact resolve eq66 eq755977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq756147 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq755977 eq3526
    | exact resolve eq3526 eq755977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq756246 : x = (k y x) := by grind
  clear eq755988
  have eq756254 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq756147
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq756147
    | exact resolve eq756147 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq756147
  have eq756392 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq755984
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq755984
    | exact resolve eq755984 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755984
  have eq756393 : x = (M.op y y) := by
    first
    | exact superpose eq755977 eq756254
    | exact resolve eq756254 eq755977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755977 eq756254
  have eq756446 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq756392 eq26
    | exact resolve eq26 eq756392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq756993 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq756246
       grind)
    | exact superpose eq756246 eq100
    | exact resolve eq100 eq756246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq756246
  have eq757149 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq756392 eq756993
    | exact resolve eq756993 eq756392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756993
  have eq757220 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq757149
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq757149
    | exact resolve eq757149 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757149
  have eq757290 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq756392 eq757220
    | exact resolve eq757220 eq756392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757220
  have eq757617 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq17112
       have i₂ := eq756393
       grind)
    | exact superpose eq756393 eq17112
    | exact resolve eq17112 eq756393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17112 eq756393
  have eq757913 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq757617
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq757617
    | exact resolve eq757617 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757617
  have eq757937 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq756392 eq757913
    | exact resolve eq757913 eq756392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757913
  have eq801795 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq757937 eq3492
    | exact resolve eq3492 eq757937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3492 eq757937
  have eq801862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq756446 eq801795
    | exact resolve eq801795 eq756446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801795
  have eq801884 : x = y := by
    first
    | (have r₁ := eq801862
       have r₂ := eq27
       grind)
    | exact resolve eq801862 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801862
  have eq801915 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq801884
       grind)
    | exact superpose eq801884 eq24
    | exact resolve eq24 eq801884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq801923 : (σ (k x (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq801884
       grind)
    | exact superpose eq801884 eq102
    | exact resolve eq102 eq801884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq801884
  have eq802993 : (σ (M.op x y)) = (σ (k x (M.op x y))) := by
    first
    | exact superpose eq757290 eq801923
    | exact resolve eq801923 eq757290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757290 eq801923
  have eq803001 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq801915
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq801915
    | exact resolve eq801915 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq801915
  have eq803163 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq45 eq802993
    | exact resolve eq802993 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq802993
  have eq803171 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq756392 eq803001
    | exact resolve eq803001 eq756392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803001
  have eq803265 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq756392 eq803163
    | exact resolve eq803163 eq756392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756392 eq803163
  have eq803343 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4835 eq803265
    | exact resolve eq803265 eq4835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835 eq803265
  have eq804017 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq803171 eq756446
    | exact resolve eq756446 eq803171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756446 eq803171
  have eq828884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq803343 eq804017
    | exact resolve eq804017 eq803343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803343 eq804017
  have eq828885 : False := by grind
  exact eq828885

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_x_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq59 X0
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq63 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq73 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq96 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq89
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
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
  have eq154 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq263 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq367 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq60
    | (have r₁ := eq60 X0 X0 X0
       have r₂ := eq59 X0
       grind)
    | exact resolve eq60 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq427 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq263 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq263
    | (have j0 := eq263 X0 y
       grind)
    | exact resolve eq263 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq263
    | (have j0 := eq263 X0 (M.op x y)
       grind)
    | exact resolve eq263 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq458 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq58
  have eq584 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq59 (σ X0)
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq59
    | (have j1 := eq83 X0 X0
       grind)
    | exact resolve eq59 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq598 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq584 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq3300 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq458 X0 X0 X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq458
    | exact resolve eq458 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq3329 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3300 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3300
    | (have j0 := eq3300 y x
       grind)
    | exact resolve eq3300 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3637 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq463 x X1 X0
       have i₂ := eq62 x x
       grind)
    | exact superpose eq62 eq463
    | exact resolve eq463 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq3659 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3637 sF0 sF0
       have i₂ := eq59 sF0
       grind)
    | exact superpose eq59 eq3637
    | exact resolve eq3637 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq3816 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq598 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq598
    | (have j0 := eq598 (τ X0)
       grind)
    | exact resolve eq598 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq598
  have eq3840 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3816 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3816
    | (have j0 := eq3816 X0
       grind)
    | exact resolve eq3816 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816
  have eq3851 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3840 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3840
    | (have j0 := eq3840 X0
       grind)
    | exact resolve eq3840 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3840
  have eq6353 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq593 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq593
    | (have j0 := eq593 x y
       grind)
    | exact resolve eq593 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6418 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6353
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6353
    | exact resolve eq6353 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6353
  have eq6504 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6418
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6418
    | exact resolve eq6418 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6418
  have eq6588 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6504
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6504
    | exact resolve eq6504 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6504
  have eq6670 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq6588
    | exact resolve eq6588 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6588
  have eq6750 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6670
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6670
    | exact resolve eq6670 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6670
  have eq6804 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6750
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6750
    | exact resolve eq6750 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6750
  have eq13491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13491
    | exact resolve eq13491 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13491
  have eq13509 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq13498
       have r₂ := eq27
       grind)
    | exact resolve eq13498 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13498
  have eq13511 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13509
    | exact resolve eq13509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13509
  have eq13519 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13511 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13511
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13511
       grind)
    | exact resolve eq13 eq13511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13511
  have eq13536 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq13519
  have eq13650 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13536 eq55
    | exact resolve eq55 eq13536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13536
  have eq13674 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq13650
    | exact resolve eq13650 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13650
  have eq13677 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq13674
       have r₂ := eq13 x y
       grind)
    | exact resolve eq13674 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13674
  have eq13686 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq13677
       grind)
    | exact superpose eq13677 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq13677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13677
  have eq13697 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13686
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13686
    | exact resolve eq13686 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13686
  have eq13709 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13697
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13697
    | exact resolve eq13697 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13697
  have eq13710 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13709
  have eq14039 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3300 x y
       have i₂ := eq13710
       grind)
    | exact superpose eq13710 eq3300
    | exact resolve eq3300 eq13710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16075 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13710
       have i₂ := eq14039
       grind)
    | exact superpose eq14039 eq13710
    | exact resolve eq13710 eq14039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13710 eq14039
  have eq16101 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16075
  have eq16118 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq16101
       grind)
    | exact superpose eq16101 eq59
    | exact resolve eq59 eq16101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16101
  have eq16148 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16118
    | exact resolve eq16118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16118
  have eq16149 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16148
  have eq16151 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16149 eq27
    | exact resolve eq27 eq16149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16154 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16149 eq73
    | (have r₁ := eq73
       have r₂ := eq16149
       grind)
    | exact resolve eq73 eq16149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq16149
  have eq16175 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16154
  have eq22229 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16175 eq101
    | exact resolve eq101 eq16175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq16175
  have eq22261 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22229
  have eq22274 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22261
       have r₂ := eq16151
       grind)
    | exact resolve eq22261 eq16151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16151 eq22261
  have eq22657 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22274 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq22274
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22274
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22274
       grind)
    | exact resolve eq13 eq22274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22274
  have eq22676 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq22657
  have eq22849 : (τ (σ x)) = (k x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22676 eq55
    | exact resolve eq55 eq22676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq22676
  have eq22883 : x = (k x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq22849
    | exact resolve eq22849 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22849
  have eq22886 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq22883
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq22883
       have r₂ := eq13 y x
       grind)
    | exact resolve eq22883 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22883
  have eq22898 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq22886
       grind)
    | exact superpose eq22886 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq22886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22886
  have eq22910 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22898
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22898
    | exact resolve eq22898 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22898
  have eq22911 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq22910
  have eq22926 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22911
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22911
    | exact resolve eq22911 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22911
  have eq22927 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq22926
  have eq23017 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3300 x y
       have i₂ := eq22927
       grind)
    | exact superpose eq22927 eq3300
    | exact resolve eq3300 eq22927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300
  have eq23132 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22927
       have i₂ := eq23017
       grind)
    | exact superpose eq23017 eq22927
    | exact resolve eq22927 eq23017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22927 eq23017
  have eq23167 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq23132
  have eq23190 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq23167
       grind)
    | exact superpose eq23167 eq59
    | exact resolve eq59 eq23167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23167
  have eq23226 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23190
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23190
    | exact resolve eq23190 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23190
  have eq23227 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23226
  have eq23229 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23227 eq20
    | exact resolve eq20 eq23227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23234 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23227 eq72
    | (have r₁ := eq72
       have r₂ := eq23227
       grind)
    | exact resolve eq72 eq23227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq23291 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23227 eq428
    | exact resolve eq428 eq23227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq23309 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23227 eq3659
    | exact resolve eq3659 eq23227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3659 eq23227
  have eq23319 : y = (k x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq23234
  have eq23326 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23291 X0
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq23291
    | exact resolve eq23291 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq23291
  have eq23380 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23229
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23229
    | exact resolve eq23229 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23229
  have eq23457 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23380 eq6804
    | exact resolve eq6804 eq23380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6804
  have eq23532 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23457
       have r₂ := eq27
       grind)
    | exact resolve eq23457 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23457
  have eq30577 : ∀ X0 : G, (k X0 (σ y)) = (σ (τ (k X0 (σ (M.op x y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23326 eq15
    | exact resolve eq15 eq23326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23326
  have eq30689 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30577 X0
       have i₂ := eq15 (k X0 sF1)
       grind)
    | exact superpose eq15 eq30577
    | exact resolve eq30577 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30577
  have eq40169 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq23319
       grind)
    | exact superpose eq23319 eq44
    | exact resolve eq44 eq23319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq23319
  have eq40213 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40169
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40169
    | exact resolve eq40169 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40169
  have eq40298 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23380 eq40213
    | exact resolve eq40213 eq23380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40330 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40213 eq30689
    | exact resolve eq30689 eq40213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30689 eq40213
  have eq40344 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq40330
  have eq40359 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq40298
  have eq43210 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq40344 eq23532
    | exact resolve eq23532 eq40344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23532 eq40344
  have eq43219 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq43210
  have eq43221 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq43219
       have r₂ := eq23380
       grind)
    | exact resolve eq43219 eq23380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23380 eq43219
  have eq45053 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq43221 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq43221
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq43221
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq43221
       grind)
    | exact resolve eq13 eq43221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43221
  have eq45080 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq45053
  have eq46149 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq45080 eq40359
    | exact resolve eq40359 eq45080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40359 eq45080
  have eq46159 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq46149
  have eq46181 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23309
       have i₂ := eq46159
       grind)
    | exact superpose eq46159 eq23309
    | exact resolve eq23309 eq46159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23309 eq46159
  have eq46226 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq46181
  have eq47053 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq46226
       grind)
    | exact superpose eq46226 eq59
    | exact resolve eq59 eq46226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq46226
  have eq47107 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq47053
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47053
    | exact resolve eq47053 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47053
  have eq47108 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq47107
  have eq47115 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47108 eq28
    | exact resolve eq28 eq47108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq47108
  have eq47361 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq47115
    | exact resolve eq47115 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47115
  have eq47362 : x = (M.op x y) := by grind
  clear eq47361
  have eq47364 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq47362 eq20
    | exact resolve eq20 eq47362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq47446 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq47362 eq3329
    | exact resolve eq3329 eq47362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3329
  have eq47488 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq47446
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47446
    | exact resolve eq47446 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq47446
  have eq47557 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq47364
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47364
    | exact resolve eq47364 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47364
  have eq47558 : x = (M.op y y) := by
    first
    | exact superpose eq47362 eq47488
    | exact resolve eq47488 eq47362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47488
  have eq47561 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq47557 eq26
    | exact resolve eq26 eq47557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq47958 : y = (M.op x x) := by
    first
    | (have i₁ := eq62 y y
       have i₂ := eq47558
       grind)
    | exact superpose eq47558 eq62
    | exact resolve eq62 eq47558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq47959 : x ≠ y ∨ x = (k x x) := by
    first
    | (have i₁ := eq367 y y
       have i₂ := eq47558
       grind)
    | exact superpose eq47558 eq367
    | exact resolve eq367 eq47558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq47558
  have eq48232 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq47958
       grind)
    | exact superpose eq47958 eq96
    | exact resolve eq96 eq47958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq47958
  have eq48308 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq47557 eq48232
    | exact resolve eq48232 eq47557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48232
  have eq48317 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq48308
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48308
    | exact resolve eq48308 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48308
  have eq53480 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq48317 eq154
    | exact resolve eq154 eq48317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53497 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq48317 eq3851
    | (have j0 := eq3851 (σ (M.op x y))
       grind)
    | exact resolve eq3851 eq48317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851 eq48317
  have eq53517 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq47561 eq53497
    | exact resolve eq53497 eq47561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53497
  have eq53525 : (τ (σ y)) = (k x x) ∨ x = y := by
    first
    | exact superpose eq47362 eq53480
    | exact resolve eq53480 eq47362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53480
  have eq53528 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq53517
       have r₂ := eq27
       grind)
    | exact resolve eq53517 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53517
  have eq53536 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq29 eq53525
    | exact resolve eq53525 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq53525
  have eq54316 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq53528 eq64
    | exact resolve eq64 eq53528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq53528
  have eq54470 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq54316 eq154
    | exact resolve eq154 eq54316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq54316
  have eq54523 : (τ (σ (M.op x y))) = (k x x) ∨ x = y := by
    first
    | exact superpose eq47362 eq54470
    | exact resolve eq54470 eq47362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54470
  have eq54532 : (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq30 eq54523
    | exact resolve eq54523 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq54523
  have eq54540 : x = (k x x) ∨ x = y := by
    first
    | exact superpose eq47362 eq54532
    | exact resolve eq54532 eq47362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47362 eq54532
  have eq54545 : x = (k x x) := by
    first
    | (have r₁ := eq54540
       have r₂ := eq47959
       grind)
    | exact resolve eq54540 eq47959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47959 eq54540
  have eq54561 : x = y ∨ x = y := by
    first
    | (have i₁ := eq53536
       have i₂ := eq54545
       grind)
    | exact superpose eq54545 eq53536
    | exact resolve eq53536 eq54545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53536
  have eq54573 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq593 x x
       have i₂ := eq54545
       grind)
    | exact superpose eq54545 eq593
    | (have j0 := eq593 x x
       grind)
    | exact resolve eq593 eq54545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq54545
  have eq54574 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq54573
  have eq54575 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq54574
  have eq54585 : x = y := by grind
  clear eq54561
  have eq54590 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq54575
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54575
    | exact resolve eq54575 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54575
  have eq54611 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq47557 eq54590
    | exact resolve eq54590 eq47557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54590
  have eq54640 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq54585
       grind)
    | exact superpose eq54585 eq24
    | exact resolve eq24 eq54585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq54585
  have eq54918 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq54640
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54640
    | exact resolve eq54640 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq54640
  have eq54995 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47557 eq54918
    | exact resolve eq54918 eq47557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47557 eq54918
  have eq55261 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq54995 eq47561
    | exact resolve eq47561 eq54995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47561 eq54995
  have eq56772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54611 eq55261
    | exact resolve eq55261 eq54611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54611 eq55261
  have eq56773 : False := by grind
  exact eq56773

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_x_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq40 X0
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq44 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq45 (M.op X0 X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq45
    | exact resolve eq45 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq28
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq28
    | exact resolve eq28 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq81 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq86 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq86
    | (have j0 := eq86 (σ X0)
       grind)
    | exact resolve eq86 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq86 (τ X0)
       grind)
    | exact superpose eq86 eq17
    | (have j1 := eq86 (τ X0)
       grind)
    | exact resolve eq17 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq86
  have eq140 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq139
    | (have j0 := eq139 X0
       grind)
    | exact resolve eq139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq148 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq162 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1 (M.op X0 X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq54
    | exact resolve eq54 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 (M.op X0 X0) (M.op x (M.op X0 x)) X1 X2
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq39 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X0 X2 (M.op X0 X1) X1
       have i₂ := eq43 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq43 eq39
    | exact resolve eq39 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq39 X1 X1 X0 X2
       grind)
    | exact superpose eq39 eq54
    | exact resolve eq54 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq562 (M.op X0 X1) X0 X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq562
    | exact resolve eq562 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq626 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq593 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq593
    | exact resolve eq593 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq148 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq148 X0 X1
       grind)
    | exact superpose eq148 eq13
    | (have j0 := eq13 (σ X0) (σ X0)
       have j1 := eq148 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq148 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq148 X0 X0
       grind)
    | exact resolve eq13 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op X2 (M.op (σ X0) X3)) (M.op (σ X0) (σ X1))) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (σ X0) X2 X3
       have i₂ := eq148 X1 X0
       grind)
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq148 X0 X0
       grind)
    | exact superpose eq148 eq9
    | (have j1 := eq148 X1 X0
       grind)
    | exact resolve eq9 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq148 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq751 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq713 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq758 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq751 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq751
    | (have j0 := eq751 X0 X1
       grind)
    | exact resolve eq751 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq808 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (M.op X1 X0)
       have i₂ := eq626 X0 X1
       grind)
    | exact superpose eq626 eq40
    | exact resolve eq40 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X1) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X0 X1 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq808 X0 X1
       grind)
    | exact superpose eq808 eq39
    | exact resolve eq39 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq849 X0 X1 X2
       have i₂ := eq626 X1 X0
       grind)
    | exact superpose eq626 eq849
    | exact resolve eq849 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq959 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq593 (M.op X2 X1) (M.op X1 (M.op X0 X1))
       have i₂ := eq869 X0 X1 X2
       grind)
    | exact superpose eq869 eq593
    | exact resolve eq593 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq965 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq959 X0 X1 X2
       have i₂ := eq626 X1 X2
       grind)
    | exact superpose eq626 eq959
    | exact resolve eq959 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1463 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq561 X0 X1 X2
       have i₂ := eq965 X0 X1 X0
       grind)
    | exact superpose eq965 eq561
    | exact resolve eq561 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq965
  have eq1473 : ∀ X0 X3 : G, (M.op X3 (M.op (M.op X0 X0) X3)) = (M.op X0 (M.op (M.op X0 X0) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1463 (M.op X0 X0) X3 (M.op x (M.op X0 x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1463
    | exact resolve eq1463 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1492 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1463 (M.op X1 X0) X0 X2
       have i₂ := eq162 X0 X1
       grind)
    | exact superpose eq162 eq1463
    | exact resolve eq1463 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1500 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1463 (M.op X2 X0) (M.op X0 X1) X2
       have i₂ := eq1463 X0 X1 X2
       grind)
    | (have i₁ := eq1463 X1 (M.op X0 X1) X2
       have i₂ := eq1463 X0 X1 X2
       grind)
    | exact superpose eq1463 eq1463
    | exact resolve eq1463 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1509 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X3 X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1463 X1 X2 X0
       have i₂ := eq1463 X1 X2 X3
       grind)
    | (have i₁ := eq1463 X0 (M.op X2 X0) X2
       have i₂ := eq1463 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1463 eq1463
    | exact resolve eq1463 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1619 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1500 X0 X1 X2 X3
       have i₂ := eq808 X0 X1
       grind)
    | exact superpose eq808 eq1500
    | exact resolve eq1500 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq1626 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1492 X0 X1 X2
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq1492
    | exact resolve eq1492 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1707 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq593 (M.op X1 (M.op X2 X0)) (M.op X0 X0)
       have i₂ := eq1626 X0 X1 X2
       grind)
    | exact superpose eq1626 eq593
    | exact resolve eq593 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1729 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1707 X0 X1 X2
       have i₂ := eq626 (M.op X2 X0) X1
       grind)
    | exact superpose eq626 eq1707
    | exact resolve eq1707 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq2069 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq81
    | (have j1 := eq132 X0
       grind)
    | exact resolve eq81 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2077 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 (σ X0) (σ X0)
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq43
    | (have j1 := eq132 X0
       grind)
    | exact resolve eq43 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2112 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq132 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq2129 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2069 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq2069
    | (have j0 := eq2069 X0
       grind)
    | exact resolve eq2069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069
  have eq2189 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1473 X0 (M.op X0 X1)
       have i₂ := eq1463 X0 X1 X0
       grind)
    | (have i₁ := eq1473 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq1463 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq1463 eq1473
    | exact resolve eq1473 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2193 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1473 X0 (M.op (M.op X2 (M.op X0 x)) (M.op X2 (M.op X0 x)))
       have i₂ := eq39 X0 X0 X2 x
       grind)
    | exact superpose eq39 eq1473
    | exact resolve eq1473 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq2298 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2193 X0 X1 X2
       have i₂ := eq162 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq162 eq2193
    | exact resolve eq2193 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2302 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2189 X0 X1
       have i₂ := eq808 X0 X1
       grind)
    | exact superpose eq808 eq2189
    | exact resolve eq2189 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq2189
  have eq2313 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2298 X0 X1 X2
       have i₂ := eq626 (M.op X1 X2) X0
       grind)
    | exact superpose eq626 eq2298
    | exact resolve eq2298 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298
  have eq2341 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2302 X2 X1
       have i₂ := eq1463 X1 X2 X0
       grind)
    | (have i₁ := eq2302 (M.op X2 X0) X0
       have i₂ := eq1463 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1463 eq2302
    | exact resolve eq2302 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302
  have eq3130 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq140 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq140
    | exact resolve eq140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq3156 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3130 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3130
    | (have j0 := eq3130 X0
       grind)
    | exact resolve eq3130 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130
  have eq3177 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (k X0 X0) X1
       have i₂ := eq3156 X0
       grind)
    | exact superpose eq3156 eq28
    | (have j1 := eq3156 X0
       grind)
    | exact resolve eq28 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3192 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3177 X0 X1
       have i₂ := eq28 (M.op X0 X0) X1
       grind)
    | exact superpose eq28 eq3177
    | (have j0 := eq3177 X0 X1
       grind)
    | exact resolve eq3177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3177
  have eq3439 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1473 X1 (M.op X1 X2)
       have i₂ := eq1509 X1 X1 X2 x
       grind)
    | (have i₁ := eq1473 X1 (M.op X1 X2)
       have i₂ := eq1509 X0 X1 X2 X1
       grind)
    | exact superpose eq1509 eq1473
    | exact resolve eq1473 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473 eq1509
  have eq3544 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3439 X0 X1 X2
       have i₂ := eq2341 X0 X1 X2
       grind)
    | exact superpose eq2341 eq3439
    | exact resolve eq3439 eq2341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341 eq3439
  have eq3715 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1619 X2 X1 X3 X4
       have i₂ := eq1463 X1 X2 X0
       grind)
    | (have i₁ := eq1619 (M.op X2 X0) X0 X2 X3
       have i₂ := eq1463 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1463 eq1619
    | exact resolve eq1619 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463 eq1619
  have eq4196 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq2129 X0
       grind)
    | exact superpose eq2129 eq81
    | (have j1 := eq2129 X0
       grind)
    | exact resolve eq81 eq2129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2129
  have eq4282 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4196 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4196
    | (have j0 := eq4196 X0
       grind)
    | exact resolve eq4196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196
  have eq4419 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq545 X0 X1 X2 X3 X4
       have i₂ := eq626 X0 X1
       grind)
    | exact superpose eq626 eq545
    | exact resolve eq545 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq4604 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X4 X0)) (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4419 (M.op X2 X0) X1 X4 (M.op X0 X0) X3
       have i₂ := eq43 X0 X2
       grind)
    | exact superpose eq43 eq4419
    | exact resolve eq4419 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6938 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op (M.op X0 X0) X2) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq537 X0 X1 X2
       have i₂ := eq626 (M.op (M.op X0 X0) X2) X1
       grind)
    | exact superpose eq626 eq537
    | exact resolve eq537 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq6975 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X3 (M.op X1 X4)) (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6938 (M.op X2 (M.op X0 X3)) X1 (M.op X0 (M.op X1 X0))
       have i₂ := eq4419 X0 X1 X2 X3 (M.op X2 (M.op X0 X3))
       grind)
    | exact superpose eq4419 eq6938
    | exact resolve eq6938 eq4419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419
  have eq10726 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (σ X3))) = X0 ∨ (σ (k X3 (τ X0))) = (M.op (σ X3) X0) ∨ (M.op X0 (σ X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq737 (τ X0) X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq737
    | exact resolve eq737 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq10939 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (σ X3))) = X0 ∨ (M.op (σ X3) X0) = (k (σ X3) X0) ∨ (M.op X0 (σ X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10726 X0 X1 X2 X3
       have i₂ := eq18 X0 X3
       grind)
    | exact superpose eq18 eq10726
    | (have j0 := eq10726 X0 X1 X2 X3
       grind)
    | exact resolve eq10726 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10726
  have eq12545 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq758 X0 X1
       have j1 := eq747 X0 X1
       grind)
    | (have r₁ := eq758 X0 X1
       have r₂ := eq747 X0 X1
       grind)
    | (have r₁ := eq758 X0 X0
       have r₂ := eq747 X0 X1
       grind)
    | exact resolve eq758 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq758
  have eq13339 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k X1 (τ X0))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12545 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12545
    | exact resolve eq12545 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12545
  have eq13481 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k X1 (τ X0))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13339 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq13339
    | (have j0 := eq13339 X0 X1
       grind)
    | exact resolve eq13339 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13339
  have eq13487 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13481 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq13481
    | (have j0 := eq13481 X0 X1
       grind)
    | exact resolve eq13481 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13481
  have eq18824 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X5 (M.op X2 (M.op X3 X0))) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq3544 X0 (M.op X3 (M.op x X1)) (M.op (M.op X0 X1) (M.op X1 X2))
       have i₂ := eq3715 X0 X1 X2 X3 x
       grind)
    | exact superpose eq3715 eq3544
    | exact resolve eq3544 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544 eq3715
  have eq18878 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X5 (M.op X2 (M.op X3 X0))) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq18824 X0 X1 X2 X3 X5
       have i₂ := eq2313 (M.op X5 (M.op X2 (M.op X3 X0))) X0 X1
       grind)
    | exact superpose eq2313 eq18824
    | exact resolve eq18824 eq2313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18824
  have eq33528 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))) = (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (M.op X2 (M.op X3 X0)) X0 (M.op X0 X1)
       have i₂ := eq18878 X0 X1 X2 X3 (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq18878 eq54
    | exact resolve eq54 eq18878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18878
  have eq33814 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 (M.op X3 X0))) = (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33528 X0 X1 X2 X3
       have i₂ := eq626 (M.op X3 X0) X2
       grind)
    | exact superpose eq626 eq33528
    | exact resolve eq33528 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33528
  have eq33875 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = (M.op X0 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33814 X0 X1 X2 X3
       have i₂ := eq1729 X0 X2 X3
       grind)
    | exact superpose eq1729 eq33814
    | exact resolve eq33814 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729 eq33814
  have eq51563 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2077 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2077
    | (have j0 := eq2077 (τ X0)
       grind)
    | exact resolve eq2077 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2077
  have eq51834 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq51563 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51563
    | (have j0 := eq51563 X0
       grind)
    | exact resolve eq51563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51563
  have eq51849 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51834 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51834
    | (have j0 := eq51834 X0
       grind)
    | exact resolve eq51834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51834
  have eq51897 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (k (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (k X0 X0) (k X0 X0)
       have i₂ := eq51849 X0
       grind)
    | exact superpose eq51849 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq51849 X0
       grind)
    | exact resolve eq13 eq51849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51849
  have eq52031 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq51897 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51897
  have eq52060 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq52031 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq52031 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq52031 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52031
  have eq52965 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (τ (k (σ X0) (σ X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (σ X0) (k (σ X0) (σ X0))
       have i₂ := eq52060 (σ X0)
       grind)
    | exact superpose eq52060 eq71
    | (have j1 := eq52060 (σ X0)
       grind)
    | exact resolve eq71 eq52060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq52982 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4282 (k X0 X0)
       have i₂ := eq52060 X0
       grind)
    | exact superpose eq52060 eq4282
    | (have j0 := eq4282 X0
       have j1 := eq52060 X0
       grind)
    | exact resolve eq4282 eq52060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4282
  have eq53020 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq52982 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52982
  have eq53027 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (k (τ (σ X0)) X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq52965 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq52965
    | (have j0 := eq52965 X0
       grind)
    | exact resolve eq52965 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq52965
  have eq53037 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq53027 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53027
    | (have j0 := eq53027 X0
       grind)
    | exact resolve eq53027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53027
  have eq53045 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53037 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq53037
    | (have j0 := eq53037 X0
       grind)
    | exact resolve eq53037 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53037
  have eq56660 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X4 X0)) (M.op X2 (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4604 X0 X1 X2 X3 X4
       have i₂ := eq2313 X1 X2 X0
       grind)
    | exact superpose eq2313 eq4604
    | exact resolve eq4604 eq2313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4604
  have eq57716 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X1 X2))) = (M.op X1 (M.op (M.op X0 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6938 X0 X1 (M.op X1 X2)
       have i₂ := eq56660 X2 (M.op X0 X0) X1 (M.op X0 X0) X1
       grind)
    | exact superpose eq56660 eq6938
    | exact resolve eq6938 eq56660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6938 eq56660
  have eq59205 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X3 (M.op X1 X4)) (M.op X0 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6975 X0 X1 X2 X3 X4
       have i₂ := eq2313 X2 X0 X1
       grind)
    | exact superpose eq2313 eq6975
    | exact resolve eq6975 eq2313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2313 eq6975
  have eq75359 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13487 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13487
    | exact resolve eq13487 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13487
  have eq78561 : ∀ X0 X1 : G, (k (k X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3192 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3192
    | (have j0 := eq3192 X1 X1
       grind)
    | exact resolve eq3192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq78723 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53020 X0
       have i₂ := eq78561 X0 X0
       grind)
    | exact superpose eq78561 eq53020
    | (have j0 := eq53020 X0
       have j1 := eq78561 X0 X0
       grind)
    | exact resolve eq53020 eq78561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53020 eq78561
  have eq78895 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78723 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq78723 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq78723 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78723
  have eq78911 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78895 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq78895
    | (have j0 := eq78895 X0
       grind)
    | exact resolve eq78895 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq78895
  have eq78918 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq78911 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq78911
    | exact resolve eq78911 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78925 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78911 (k X0 X0)
       have i₂ := eq52060 X0
       grind)
    | exact superpose eq52060 eq78911
    | (have j0 := eq78911 X0
       have j1 := eq52060 X0
       grind)
    | exact resolve eq78911 eq52060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52060 eq78911
  have eq79045 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78925 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78925
  have eq79889 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X1 (M.op X2 (k X0 X0))) X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1626 (k X0 X0) X1 X2
       have i₂ := eq79045 X0
       grind)
    | exact superpose eq79045 eq1626
    | (have j1 := eq79045 X0
       grind)
    | exact resolve eq1626 eq79045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626 eq79045
  have eq96646 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 (σ X0)
       have i₂ := eq78918 X0
       grind)
    | exact superpose eq78918 eq40
    | (have j1 := eq78918 X0
       grind)
    | exact resolve eq40 eq78918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78918
  have eq798457 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op (M.op X2 X3) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    by_contra hcon
    push Not at hcon
    have f798457_12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X1 X2))) = (M.op X1 (M.op (M.op X0 X0) (M.op X1 X2))) := by
      intro X0 X1 X2
      grind
    have f798457_13 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X3 (M.op X1 X4)) (M.op X0 (M.op X2 (M.op X0 X1)))) := by
      intro X0 X1 X2 X3 X4
      grind
    have f798457_22 : (M.op X1 (M.op X0 (M.op X1 X2))) ≠ (M.op (M.op X2 X3) (M.op X0 (M.op X1 X2))) := by grind
    have f798457_111 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op (M.op X2 X3) (M.op X0 (M.op X1 X2))) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f798457_12 (M.op X1 x) X0 (M.op X2 (M.op X0 X1))
         have i₂ := f798457_13 X0 X1 X2 (M.op X1 x) x
         grind)
      | exact superpose f798457_13 f798457_12
      | exact resolve f798457_12 f798457_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f798457_630 : (M.op X1 (M.op X0 (M.op X1 X2))) ≠ (M.op X1 (M.op X0 (M.op X1 X2))) := by
      first
      | (have i₁ := f798457_22
         have i₂ := f798457_111 X0 X1 X2 X3
         grind)
      | exact superpose f798457_111 f798457_22
      | (have r₁ := f798457_22
         have r₂ := f798457_111 X0 X1 X2 X3
         grind)
      | exact resolve f798457_22 f798457_111
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f798457_663 : False := by grind
    exact f798457_663
  clear eq59205
  have eq802649 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op X3 X0))) = (M.op X2 (M.op (M.op X2 X2) (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57716 X2 X3 X0
       have i₂ := eq798457 (M.op X2 X2) X3 X0 X1
       grind)
    | (have i₁ := eq57716 X0 (M.op X2 X3) X2
       have i₂ := eq798457 (M.op X0 X0) (M.op X2 X3) X2 X3
       grind)
    | exact superpose eq798457 eq57716
    | exact resolve eq57716 eq798457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57716 eq798457
  have eq805124 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X2 X2) (M.op X3 X0))) = (M.op X0 (M.op (M.op X2 X2) (M.op X3 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq802649 X0 x X2 X3
       have i₂ := eq33875 X0 x (M.op X2 X2) X3
       grind)
    | exact superpose eq33875 eq802649
    | exact resolve eq802649 eq33875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33875 eq802649
  have eq824917 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75359 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75359
  have eq901807 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq824917 (M.op X0 X1) X0
       have i₂ := eq593 X0 X1
       grind)
    | exact superpose eq593 eq824917
    | (have j0 := eq824917 X0 X0
       grind)
    | (have r₁ := eq824917 (M.op X0 X1) X0
       have r₂ := eq593 X0 X1
       grind)
    | exact resolve eq824917 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902258 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq901807 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901807
  have eq903936 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq902258 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq902258
    | exact resolve eq902258 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq902258
  have eq904797 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq903936 X0 X1
       have i₂ := eq626 X0 X1
       grind)
    | exact superpose eq626 eq903936
    | (have j0 := eq903936 X0 X1
       grind)
    | exact resolve eq903936 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq903936
  have eq904918 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq904797 X0 X1
       have i₂ := eq162 X0 X1
       grind)
    | exact superpose eq162 eq904797
    | (have j0 := eq904797 X0 X1
       grind)
    | exact resolve eq904797 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904797
  have eq1310730 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (σ X2) X0) ∨ (k (σ X2) X0) = (M.op (σ X2) X0) ∨ (M.op X0 (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq805124 (σ x) (M.op X0 X2) X0
       have i₂ := eq10939 X0 (M.op X0 X2) X2 x
       grind)
    | exact superpose eq10939 eq805124
    | (have j1 := eq10939 X0 X1 X2 X2
       grind)
    | exact resolve eq805124 eq10939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10939 eq805124
  have eq1313675 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op (σ X2) X0) ∨ (k (σ X2) X0) = (M.op (σ X2) X0) ∨ (M.op X0 (σ X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq1310730 X0 x X2
       have i₂ := eq593 X0 x
       grind)
    | exact superpose eq593 eq1310730
    | (have j0 := eq1310730 X0 x X2
       grind)
    | exact resolve eq1310730 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq1310730
  have eq1314135 : ∀ X0 X2 : G, (k (σ X2) X0) = (M.op (σ X2) X0) ∨ (M.op X0 (σ X2)) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq1313675 X0 X2
       have j1 := eq824917 (σ X2) X0
       grind)
    | (have r₁ := eq1313675 x X2
       have r₂ := eq824917 (σ X2) x
       grind)
    | (have r₁ := eq1313675 (σ X2) X2
       have r₂ := eq824917 (σ X2) (σ X2)
       grind)
    | (have r₁ := eq1313675 (M.op (σ X2) (σ X2)) X2
       have r₂ := eq824917 (M.op (σ X2) (σ X2)) (σ X2)
       grind)
    | exact resolve eq1313675 eq824917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313675
  have eq1314291 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1314135 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1314135
    | exact resolve eq1314135 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1314413 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1314135 (σ X1) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1314135
    | (have j0 := eq1314135 (σ X1) X0
       grind)
    | exact resolve eq1314135 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314135
  have eq1339503 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1314413 x y
       grind)
    | exact superpose eq1314413 eq16
    | (have j1 := eq1314413 x y
       grind)
    | exact resolve eq16 eq1314413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314413
  have eq1341407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1339503
       have i₂ := eq1314291 x y
       grind)
    | exact superpose eq1314291 eq1339503
    | (have j1 := eq1314291 (σ x) (σ y)
       grind)
    | exact resolve eq1339503 eq1314291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339503
  have eq1341412 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq1341407
  have eq1341554 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq1341412
       grind)
    | exact superpose eq1341412 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1341412
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1341412
       grind)
    | exact resolve eq12 eq1341412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341412
  have eq1341878 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1341554
  have eq1341983 : (σ x) = (σ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1341878
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1341878
    | exact resolve eq1341878 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341878
  have eq1342076 : (k x y) = (τ (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1341983
       grind)
    | exact superpose eq1341983 eq10
    | exact resolve eq10 eq1341983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341983
  have eq1342645 : x = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1342076
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1342076
    | exact resolve eq1342076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342076
  have eq1342646 : x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1342645
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1342645 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342645
  have eq1342653 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1342646
       have i₂ := eq1314291 x y
       grind)
    | exact superpose eq1314291 eq1342646
    | (have j1 := eq1314291 x y
       grind)
    | exact resolve eq1342646 eq1314291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314291
  have eq1343013 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq904918 x y
       have i₂ := eq1342653
       grind)
    | exact superpose eq1342653 eq904918
    | exact resolve eq904918 eq1342653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904918 eq1342653
  have eq1343043 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1343013
       have i₂ := eq1342646
       grind)
    | exact superpose eq1342646 eq1343013
    | exact resolve eq1343013 eq1342646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342646 eq1343013
  have eq1343044 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1343043
  have eq1343177 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1343044
       grind)
    | exact superpose eq1343044 eq40
    | exact resolve eq40 eq1343044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1343044
  have eq1343836 : x = (M.op x y) := by grind
  clear eq1343177
  have eq1343897 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq162 y x
       have i₂ := eq1343836
       grind)
    | exact superpose eq1343836 eq162
    | exact resolve eq162 eq1343836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq1344266 : x = (M.op y y) := by
    first
    | (have i₁ := eq1343897
       have i₂ := eq1343836
       grind)
    | exact superpose eq1343836 eq1343897
    | exact resolve eq1343897 eq1343836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343897
  have eq1344339 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op x X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 y X1 x
       have i₂ := eq1344266
       grind)
    | exact superpose eq1344266 eq54
    | exact resolve eq54 eq1344266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1344952 : x ≠ x ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq824917 y y
       have i₂ := eq1344266
       grind)
    | exact superpose eq1344266 eq824917
    | exact resolve eq824917 eq1344266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824917 eq1344266
  have eq1344986 : x = (k y y) ∨ x = y := by grind
  clear eq1344952
  have eq1397073 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1344339 x (k y y)
       have i₂ := eq79889 y x x
       grind)
    | exact superpose eq79889 eq1344339
    | (have j1 := eq79889 y x x
       grind)
    | exact resolve eq1344339 eq79889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79889 eq1344339
  have eq1478389 : x ≠ y ∨ x = (k y y) := by grind
  clear eq1397073
  have eq1478468 : x = (k y y) := by
    first
    | (have r₁ := eq1478389
       have r₂ := eq1344986
       grind)
    | exact resolve eq1478389 eq1344986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344986 eq1478389
  have eq1478862 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2112 y
       have i₂ := eq1478468
       grind)
    | exact superpose eq1478468 eq2112
    | (have j0 := eq2112 y
       grind)
    | exact resolve eq2112 eq1478468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112
  have eq1478995 : y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq53045 y
       have i₂ := eq1478468
       grind)
    | exact superpose eq1478468 eq53045
    | exact resolve eq53045 eq1478468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53045 eq1478468
  have eq1505553 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96646 x
       have i₂ := eq1478995
       grind)
    | exact superpose eq1478995 eq96646
    | exact resolve eq96646 eq1478995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96646 eq1478995
  have eq1506289 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1505553
  have eq1878686 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1506289
       grind)
    | exact superpose eq1506289 eq16
    | exact resolve eq16 eq1506289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506289
  have eq1879307 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1878686
       have i₂ := eq1343836
       grind)
    | exact superpose eq1343836 eq1878686
    | exact resolve eq1878686 eq1343836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878686
  have eq1879308 : (σ x) = (σ y) := by grind
  clear eq1879307
  have eq1879436 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1879308
       grind)
    | exact superpose eq1879308 eq16
    | exact resolve eq16 eq1879308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1879439 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1478862
       have i₂ := eq1879308
       grind)
    | exact superpose eq1879308 eq1478862
    | (have r₁ := eq1478862
       have r₂ := eq1879308
       grind)
    | exact resolve eq1478862 eq1879308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478862 eq1879308
  have eq1880179 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1879439
  have eq1880322 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1879436
       have i₂ := eq1343836
       grind)
    | exact superpose eq1343836 eq1879436
    | exact resolve eq1879436 eq1343836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343836 eq1879436
  have eq1891595 : False := by grind
  exact eq1891595
