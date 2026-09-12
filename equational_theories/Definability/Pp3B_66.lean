import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq32 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq36 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq36 X0 X1
       grind)
    | exact resolve eq42 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq42
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45
  have eq93 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq97 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq93 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq93 X1 X1
       have r₂ := eq47 X1 X1
       grind)
    | exact resolve eq93 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq93
  have eq247 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq97 (σ X0) (σ X1)
       grind)
    | exact superpose eq97 eq15
    | exact resolve eq15 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq247 X0 X1
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq247
    | exact resolve eq247 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq247
  have eq257 : False := by grind
  exact eq257

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_x_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X0)
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq21 X1 X1
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq209 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq213 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq227 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq213 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq213 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq213 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq231 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq227 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq227
    | (have j0 := eq227 X0 X1
       grind)
    | exact resolve eq227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq259 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq405 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq438 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq405
    | (have j0 := eq405 X0 X1
       grind)
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq750 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq209
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq209
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq209 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq751 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq750
  have eq830 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq231 X0 (M.op X0 X0)
       have i₂ := eq259 X0
       grind)
    | exact superpose eq259 eq231
    | (have j0 := eq231 X0 (M.op X0 X0)
       grind)
    | exact resolve eq231 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq259
  have eq851 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq852 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq883 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0) (σ X0)
       have i₂ := eq852 X0
       grind)
    | exact superpose eq852 eq21
    | exact resolve eq21 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13802 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq14009 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13802 X0 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq13802
    | (have j0 := eq13802 X0 X1
       grind)
    | exact resolve eq13802 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq13802
  have eq15311 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14009 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14009
    | (have j0 := eq14009 (σ X0) (σ X1)
       grind)
    | exact resolve eq14009 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14009
  have eq15439 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15311 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq15311
    | (have j0 := eq15311 X0 X1
       grind)
    | exact resolve eq15311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15311
  have eq15452 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15439 X0 X1
       have i₂ := eq852 X0
       grind)
    | exact superpose eq852 eq15439
    | (have j0 := eq15439 X0 X1
       grind)
    | exact resolve eq15439 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15439
  have eq20384 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq751
       grind)
    | exact superpose eq751 eq9
    | exact resolve eq9 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq20445 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq20384 X0
       have i₂ := eq852 y
       grind)
    | exact superpose eq852 eq20384
    | (have j0 := eq20384 X0
       grind)
    | exact resolve eq20384 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20384
  have eq225436 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq15452 X0 X1
       grind)
    | exact superpose eq15452 eq11
    | (have j1 := eq15452 X0 X1
       grind)
    | exact resolve eq11 eq15452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15452
  have eq257462 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq225436 y x
       grind)
    | exact superpose eq225436 eq16
    | (have j1 := eq225436 y x
       grind)
    | exact resolve eq16 eq225436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225436
  have eq258999 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq257462
       have i₂ := eq438 y x
       grind)
    | exact superpose eq438 eq257462
    | (have j1 := eq438 y x
       grind)
    | (have r₁ := eq257462
       have r₂ := eq438 y x
       grind)
    | exact resolve eq257462 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq257462
  have eq259000 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq258999
  have eq409349 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq20445 y
       have i₂ := eq259000
       grind)
    | exact superpose eq259000 eq20445
    | exact resolve eq20445 eq259000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20445
  have eq409488 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq409349
  have eq806577 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq409488
       grind)
    | exact superpose eq409488 eq16
    | exact resolve eq16 eq409488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409488
  have eq806902 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq806577
       have i₂ := eq259000
       grind)
    | exact superpose eq259000 eq806577
    | exact resolve eq806577 eq259000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259000 eq806577
  have eq806906 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq806902
  have eq806907 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq806906
  have eq809209 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq806907
       grind)
    | exact superpose eq806907 eq9
    | exact resolve eq9 eq806907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818844 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq809209 (σ y)
       have i₂ := eq806907
       grind)
    | exact superpose eq806907 eq809209
    | exact resolve eq809209 eq806907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809209
  have eq819056 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq818844
  have eq819088 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq819056
       have i₂ := eq852 y
       grind)
    | exact superpose eq852 eq819056
    | exact resolve eq819056 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852 eq819056
  have eq821371 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq806907
       have i₂ := eq819088
       grind)
    | exact superpose eq819088 eq806907
    | exact resolve eq806907 eq819088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806907 eq819088
  have eq821597 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq821371
  have eq821737 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq821597
       grind)
    | exact superpose eq821597 eq10
    | exact resolve eq10 eq821597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821597
  have eq822262 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq821737
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq821737
    | exact resolve eq821737 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821737
  have eq822263 : x = (M.op y y) := by grind
  clear eq822262
  have eq824690 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq883 y
       have i₂ := eq822263
       grind)
    | exact superpose eq822263 eq883
    | exact resolve eq883 eq822263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq825008 : x = (M.op x y) := by
    first
    | (have i₁ := eq21 y y
       have i₂ := eq822263
       grind)
    | exact superpose eq822263 eq21
    | exact resolve eq21 eq822263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq822263
  have eq834876 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq824690
       grind)
    | exact superpose eq824690 eq16
    | exact resolve eq16 eq824690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824690
  have eq835143 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq834876
       have i₂ := eq825008
       grind)
    | exact superpose eq825008 eq834876
    | exact resolve eq834876 eq825008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825008 eq834876
  have eq835144 : False := by grind
  exact eq835144

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pyy_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  clear eq18
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
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq14
    | (have j0 := eq14 (τ X1) (τ X0)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op (σ X0) (σ X1)) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X1) (σ X0)
       have i₂ := eq468 X0 X1
       grind)
    | (have i₁ := eq63 (σ X0) (σ X1)
       have i₂ := eq468 X0 X1
       grind)
    | exact superpose eq468 eq63
    | (have j1 := eq468 X0 X1
       grind)
    | exact resolve eq63 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq746 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq468 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq468 X0 X1
       grind)
    | exact superpose eq468 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq468 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq468 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq468 X0 X1
       grind)
    | exact resolve eq13 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq760 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq746 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq761 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq760 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq766 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq761 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq761
    | (have j0 := eq761 X0 X1
       grind)
    | exact resolve eq761 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq12861 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq766 (τ X0) (τ X1)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq766
    | (have j0 := eq766 (τ X1) (τ X0)
       grind)
    | exact resolve eq766 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq13023 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12861 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12861
    | (have j0 := eq12861 X0 X1
       grind)
    | exact resolve eq12861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12861
  have eq13064 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13023 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq13023
    | (have j0 := eq13023 X0 X1
       grind)
    | exact resolve eq13023 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13023
  have eq13102 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13064 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq13064
    | (have j0 := eq13064 X0 X1
       grind)
    | exact resolve eq13064 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13064
  have eq13134 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13102 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13102
    | (have j0 := eq13102 X0 X1
       grind)
    | exact resolve eq13102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13102
  have eq13159 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13134 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13134
    | (have j0 := eq13134 X0 X1
       grind)
    | exact resolve eq13134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13134
  have eq13180 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13159 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13159
    | (have j0 := eq13159 X0 X1
       grind)
    | exact resolve eq13159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13159
  have eq13197 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13180 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq13180
    | (have j0 := eq13180 X0 X1
       grind)
    | exact resolve eq13180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13180
  have eq13228 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13197 (τ X1) (τ X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq13197
    | (have j0 := eq13197 (τ (k X0 X1)) (τ X1)
       grind)
    | exact resolve eq13197 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13197
  have eq59330 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (M.op (M.op (σ X1) X0) X0) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq734
    | exact resolve eq734 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq59467 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (M.op (M.op (σ X1) X0) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq59330 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq59330
    | (have j0 := eq59330 X0 X1
       grind)
    | exact resolve eq59330 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq59330
  have eq59492 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59467 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59467
    | exact resolve eq59467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59467
  have eq59730 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq59492 X0 X1
       grind)
    | exact superpose eq59492 eq9
    | (have j1 := eq59492 X0 X1
       grind)
    | exact resolve eq9 eq59492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59960 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59492 X1 X0
       have i₂ := eq59730 X1 X0
       grind)
    | exact superpose eq59730 eq59492
    | (have j0 := eq59492 X1 X0
       have j1 := eq59730 X1 X0
       grind)
    | exact resolve eq59492 eq59730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59492 eq59730
  have eq60065 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq59960 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59960
  have eq86845 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (M.op (τ X1) (τ X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq469 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq87401 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (M.op (τ X0) (τ X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86845 X0 X1
       have i₂ := eq60065 (τ X0) (τ X1)
       grind)
    | (have i₁ := eq86845 X1 X1
       have i₂ := eq60065 (τ X1) X1
       grind)
    | exact superpose eq60065 eq86845
    | (have j0 := eq86845 X0 X1
       have j1 := eq60065 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq86845 X1 X1
       have r₂ := eq60065 (τ X1) (τ (k X1 X1))
       grind)
    | exact resolve eq86845 eq60065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60065 eq86845
  have eq87403 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (M.op (τ X0) (τ X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87401 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87401
  have eq87405 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87403 X0 X1
       have j1 := eq13228 X1 X0
       grind)
    | (have r₁ := eq87403 X1 X0
       have r₂ := eq13228 X0 X1
       grind)
    | (have r₁ := eq87403 X1 X1
       have r₂ := eq13228 (k X1 X1) X1
       grind)
    | (have r₁ := eq87403 X0 X0
       have r₂ := eq13228 X0 X0
       grind)
    | exact resolve eq87403 eq13228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13228 eq87403
  have eq87415 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87405 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq87405
    | (have j0 := eq87405 X0 X1
       grind)
    | exact resolve eq87405 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq87405
  have eq87416 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87415 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87415
  have eq87438 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq87416 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87416
    | exact resolve eq87416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87416
  have eq87866 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq87438 X0 X1
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq87438
    | (have j0 := eq87438 X0 X1
       grind)
    | exact resolve eq87438 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq87438
  have eq87936 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87866 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87866
    | exact resolve eq87866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87866
  have eq88405 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87936 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq87936
    | (have j0 := eq87936 (σ X0) (σ X1)
       grind)
    | exact resolve eq87936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88865 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88405 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88405
  have eq89931 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88865 X1 X0
       have i₂ := eq87936 X1 X0
       grind)
    | exact superpose eq87936 eq88865
    | (have j0 := eq88865 X1 X0
       have j1 := eq87936 (σ X1) (σ X0)
       grind)
    | exact resolve eq88865 eq87936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96339 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89931 x y
       grind)
    | exact superpose eq89931 eq16
    | (have j1 := eq89931 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq89931 x y
       grind)
    | exact resolve eq16 eq89931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89931
  have eq96459 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq96339
  have eq96651 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq96459
  have eq96775 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96651
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq96651
    | exact resolve eq96651 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96651
  have eq96811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq87936 eq96775
    | (have j1 := eq87936 y x
       grind)
    | exact resolve eq96775 eq87936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87936 eq96775
  have eq96838 : y = (M.op x x) := by
    first
    | (have r₁ := eq96811
       have r₂ := eq16
       grind)
    | exact resolve eq96811 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96811
  have eq96841 : (M.op x y) = (k y x) := by grind
  clear eq96838
  have eq97050 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq88865 y x
       have i₂ := eq96841
       grind)
    | exact superpose eq96841 eq88865
    | (have j0 := eq88865 y x
       grind)
    | exact resolve eq88865 eq96841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88865
  have eq97051 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq97050
       have r₂ := eq16
       grind)
    | exact resolve eq97050 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97050
  have eq97237 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq97051
  have eq97361 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq97237
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq97237
    | exact resolve eq97237 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97237
  have eq97397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97361
       have i₂ := eq96841
       grind)
    | exact superpose eq96841 eq97361
    | exact resolve eq97361 eq96841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96841 eq97361
  have eq97423 : False := by grind
  exact eq97423

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_y_pxx_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op x X1)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq40
    | exact resolve eq40 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq180
    | exact resolve eq180 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq195 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq178 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 x y
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 (M.op X1 X0) X1
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq141
    | exact resolve eq141 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq239
    | exact resolve eq239 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq267 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq152
    | exact resolve eq152 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq288 : y = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq31 eq267
    | exact resolve eq267 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq361 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq450 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq361
    | exact resolve eq361 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq658 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ x)))) = (k (τ X0) (k y x)) := by
    intro X0
    first
    | exact superpose eq114 eq450
    | exact resolve eq450 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq725 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X1)
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq11
    | (have j0 := eq11 X1 (M.op X1 X0)
       grind)
    | exact resolve eq11 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq730
       have i₂ := eq195
       grind)
    | exact superpose eq195 eq730
    | exact resolve eq730 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq730
  have eq773 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq11 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X1 ∨ (M.op X1 X1) = (k X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq12
    | (have j0 := eq12 X1 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq773 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq784 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq782 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq782 X1 X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq782 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq782 (M.op X1 X1) X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq782 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq811 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0 X0
       have i₂ := eq781 X0
       grind)
    | exact superpose eq781 eq178
    | (have j1 := eq781 X0
       grind)
    | exact resolve eq178 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq1468 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq762
       grind)
    | exact superpose eq762 eq39
    | exact resolve eq39 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1469 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1468
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1468
    | exact resolve eq1468 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1471 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1469
    | exact resolve eq1469 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq2890 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq784 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq784
    | (have j0 := eq784 X1 X0
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq784 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq784 X1 X1
       have r₂ := eq11 (k X1 X1) X1
       grind)
    | exact resolve eq784 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq2907 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2890 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq2890 X1 (M.op X1 X1)
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq2890 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq2890 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2890 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq17200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1471 eq732
    | exact resolve eq732 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17209 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17200
       have r₂ := eq27
       grind)
    | exact resolve eq17200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17200
  have eq17222 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17209 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17209
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17209
       grind)
    | exact resolve eq12 eq17209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17225 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17209 eq178
    | exact resolve eq178 eq17209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17209
  have eq17238 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by grind
  clear eq17222
  have eq17243 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq17225
    | exact resolve eq17225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17225
  have eq17245 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17238
       have r₂ := eq26
       grind)
    | exact resolve eq17238 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17238
  have eq17250 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1471 eq17245
    | exact resolve eq17245 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471 eq17245
  have eq17253 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17243 eq176
    | exact resolve eq176 eq17243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17279 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17243 eq17253
    | exact resolve eq17253 eq17243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17243 eq17253
  have eq17289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17250 eq17279
    | exact resolve eq17279 eq17250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17250 eq17279
  have eq17294 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17289
       have r₂ := eq27
       grind)
    | exact resolve eq17289 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17289
  have eq17296 : x = (k (τ (σ y)) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17294 eq260
    | exact resolve eq260 eq17294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17299 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17294 eq174
    | exact resolve eq174 eq17294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17319 : x = (k y x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17296
    | exact resolve eq17296 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17296
  have eq17320 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq17319
       have r₂ := eq13 y x
       grind)
    | exact resolve eq17319 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17319
  have eq17324 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k y x) := by
    first
    | exact superpose eq17320 eq175
    | exact resolve eq175 eq17320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17320
  have eq17338 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq17324
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17324
    | exact resolve eq17324 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17324
  have eq17344 : (M.op y y) = (M.op (M.op x y) y) ∨ x = (k y x) := by
    first
    | exact superpose eq17338 eq175
    | exact resolve eq175 eq17338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17362 : (M.op x y) = (M.op y y) ∨ x = (k y x) := by
    first
    | exact superpose eq17338 eq17344
    | exact resolve eq17344 eq17338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17338 eq17344
  have eq17372 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ y = (k X0 y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq17362
       grind)
    | exact superpose eq17362 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq17362
       grind)
    | exact resolve eq13 eq17362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17374 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq17362
       grind)
    | exact superpose eq17362 eq12
    | exact resolve eq12 eq17362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17362
  have eq17386 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq17374
  have eq17468 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq17386
       grind)
    | exact superpose eq17386 eq40
    | exact resolve eq40 eq17386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17476 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq17468
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17468
    | exact resolve eq17468 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17468
  have eq17480 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq17476
    | exact resolve eq17476 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17476
  have eq17501 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq17480 eq811
    | (have j0 := eq811 (σ y)
       grind)
    | exact resolve eq811 eq17480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17480
  have eq17717 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (k y x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq17299 eq658
    | exact resolve eq658 eq17299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq17299
  have eq17730 : ∀ X0 : G, (k (τ X0) x) = (k (τ X0) (k y x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq141 eq17717
    | exact resolve eq17717 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq17717
  have eq17733 : ∀ X0 : G, (k (τ X0) x) = (k (τ X0) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq762 eq17730
    | exact resolve eq17730 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17730
  have eq20751 : y = (k (τ (σ y)) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq17501 eq288
    | exact resolve eq288 eq17501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17501
  have eq20763 : y = (k y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq31 eq20751
    | exact resolve eq20751 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20751
  have eq20765 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y y) ∨ x = (k y x) := by
    first
    | (have j1 := eq17372 y
       grind)
    | (have r₁ := eq20763
       have r₂ := eq17372 y
       grind)
    | exact resolve eq20763 eq17372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17372 eq20763
  have eq20772 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ y = (k y y) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq20765 eq16
    | exact resolve eq16 eq20765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25298 : (k y x) = (k y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17733
    | exact resolve eq17733 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25309 : x = (k (τ (M.op (σ x) (σ x))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq260
       have i₂ := eq17733 (M.op sF2 sF2)
       grind)
    | exact superpose eq17733 eq260
    | exact resolve eq260 eq17733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17733
  have eq25328 : x = (k (τ (σ y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17294 eq25309
    | exact resolve eq25309 eq17294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17294 eq25309
  have eq25337 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq762 eq25298
    | exact resolve eq25298 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq25298
  have eq25369 : x = (k y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq25328
    | exact resolve eq25328 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25328
  have eq25376 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25337 eq25369
    | exact resolve eq25369 eq25337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25337 eq25369
  have eq25393 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25376 eq175
    | exact resolve eq175 eq25376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25396 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op x y) X0) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq25376 eq16
    | exact resolve eq16 eq25376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25418 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25393
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25393
    | exact resolve eq25393 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25393
  have eq25437 : (M.op y y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25418 eq175
    | exact resolve eq175 eq25418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25463 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25418 eq25437
    | exact resolve eq25437 eq25418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25418 eq25437
  have eq25482 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq25463
       grind)
    | exact superpose eq25463 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq25463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25498 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq25482
  have eq25623 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq25498
       grind)
    | exact superpose eq25498 eq40
    | exact resolve eq40 eq25498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25638 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25623
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25623
    | exact resolve eq25623 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25623
  have eq25642 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq25638
    | exact resolve eq25638 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25638
  have eq26133 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25376 eq25396
    | exact resolve eq25396 eq25376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25396
  have eq26181 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq26133
  have eq26190 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25376 eq26181
    | exact resolve eq26181 eq25376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25376 eq26181
  have eq26207 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq26190
       grind)
    | exact superpose eq26190 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq26190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26222 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq26225 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ y = (M.op x x) := by grind
  clear eq26207
  have eq26226 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq26225
  have eq26296 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq26226
       grind)
    | exact superpose eq26226 eq39
    | exact resolve eq39 eq26226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq26320 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26296
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26296
    | exact resolve eq26296 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26296
  have eq26324 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq26320
    | exact resolve eq26320 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26320
  have eq26730 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26324 eq811
    | (have j0 := eq811 (σ x)
       grind)
    | exact resolve eq811 eq26324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29309 : x = (k (τ (σ x)) x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26730 eq260
    | exact resolve eq260 eq26730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq26730
  have eq29334 : x = (k x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq29309
    | exact resolve eq29309 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29309
  have eq29338 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26226 eq29334
    | exact resolve eq29334 eq26226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26226 eq29334
  have eq29339 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq29338
  have eq36840 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29339 eq20772
    | exact resolve eq20772 eq29339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20772 eq29339
  have eq36911 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y y) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq36840
       have r₂ := eq13 y x
       grind)
    | exact resolve eq36840 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36840
  have eq36921 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y y) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq36911
    | exact resolve eq36911 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36911
  have eq36927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20765 eq36921
    | exact resolve eq36921 eq20765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20765 eq36921
  have eq36932 : y = (k y y) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36927
       have r₂ := eq27
       grind)
    | exact resolve eq36927 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36927
  have eq36956 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17386
       have i₂ := eq36932
       grind)
    | exact superpose eq36932 eq17386
    | exact resolve eq17386 eq36932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17386
  have eq36967 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25498
       have i₂ := eq36932
       grind)
    | exact superpose eq36932 eq25498
    | exact resolve eq25498 eq36932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25498 eq36932
  have eq36992 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by grind
  clear eq36967
  have eq36999 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq36956
  have eq37023 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq36992
       have r₂ := eq26222
       grind)
    | exact resolve eq36992 eq26222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36992
  have eq37032 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq37023
       have r₂ := eq13 y x
       grind)
    | exact resolve eq37023 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37023
  have eq37045 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq37032
       grind)
    | exact superpose eq37032 eq36
    | exact resolve eq36 eq37032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37053 : x ≠ (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2907 x y
       have i₂ := eq37032
       grind)
    | exact superpose eq37032 eq2907
    | (have j0 := eq2907 x y
       grind)
    | exact resolve eq2907 eq37032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37032
  have eq37055 : x ≠ (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq37053
  have eq37059 : x ≠ (k x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25463 eq37055
    | exact resolve eq37055 eq25463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25463 eq37055
  have eq37060 : x ≠ (k x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq37059
  have eq37068 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37045
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37045
    | exact resolve eq37045 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37045
  have eq37081 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37068 eq732
    | exact resolve eq732 eq37068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq39328 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37081 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq37081
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq37081
       grind)
    | exact resolve eq12 eq37081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39331 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37081 eq178
    | exact resolve eq178 eq37081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq37081
  have eq39357 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39328
  have eq39370 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq39331
    | exact resolve eq39331 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39331
  have eq39372 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq39357
       have r₂ := eq26
       grind)
    | exact resolve eq39357 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39357
  have eq39379 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37068 eq39372
    | exact resolve eq39372 eq37068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37068 eq39372
  have eq39388 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39370 eq176
    | exact resolve eq176 eq39370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39433 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39370 eq39388
    | exact resolve eq39388 eq39370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39370 eq39388
  have eq39445 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39379 eq39433
    | exact resolve eq39433 eq39379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39379 eq39433
  have eq39446 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39445
  have eq39482 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39446 eq12
    | exact resolve eq12 eq39446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39486 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39446 eq197
    | exact resolve eq197 eq39446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39489 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39446 eq725
    | exact resolve eq725 eq39446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39493 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39446 eq774
    | exact resolve eq774 eq39446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39446
  have eq39504 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39482
  have eq39522 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq39493
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq39493 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39493
  have eq39523 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq39489
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq39489 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39489
  have eq39524 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq39486
    | exact resolve eq39486 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39486
  have eq39528 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq39522
    | exact resolve eq39522 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39522
  have eq39529 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq39523
    | exact resolve eq39523 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39523
  have eq39530 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq39529
       have r₂ := eq39528
       grind)
    | exact resolve eq39529 eq39528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39528 eq39529
  have eq41318 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39524 eq12
    | exact resolve eq12 eq39524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41325 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39524 eq725
    | exact resolve eq725 eq39524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41329 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39524 eq774
    | exact resolve eq774 eq39524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39524
  have eq41341 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq41318
  have eq41343 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq41329
       have r₂ := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq41329 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41329
  have eq41344 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq41325
       have r₂ := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq41325 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41325
  have eq41351 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq41344
       have r₂ := eq41343
       grind)
    | exact resolve eq41344 eq41343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41343 eq41344
  have eq41373 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39530 eq90
    | exact resolve eq90 eq39530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq39530
  have eq41381 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq41373
    | exact resolve eq41373 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41373
  have eq41446 : (τ (M.op (σ x) (σ y))) = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41351 eq107
    | exact resolve eq107 eq41351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq41351
  have eq41463 : x ≠ y ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37060
       have i₂ := eq41381
       grind)
    | exact superpose eq41381 eq37060
    | exact resolve eq37060 eq41381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37060 eq41381
  have eq41471 : x ≠ y ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41463
  have eq41681 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39504 eq97
    | exact resolve eq97 eq39504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39504
  have eq41736 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq41681
    | exact resolve eq41681 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41681
  have eq41845 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41341 eq25642
    | exact resolve eq25642 eq41341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41845
  have eq41891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41874
       have r₂ := eq26222
       grind)
    | exact resolve eq41874 eq26222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41874
  have eq41912 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41891
       have r₂ := eq27
       grind)
    | exact resolve eq41891 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41891
  have eq42150 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq41912
       grind)
    | exact superpose eq41912 eq12
    | exact resolve eq12 eq41912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41912
  have eq42173 : x = y ∨ y = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq42150
  have eq42184 : x = y ∨ y = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41736 eq42173
    | exact resolve eq42173 eq41736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41736 eq42173
  have eq42185 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq42184
  have eq43358 : y ≠ y ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2907 x x
       have i₂ := eq42185
       grind)
    | exact superpose eq42185 eq2907
    | (have j0 := eq2907 x x
       grind)
    | exact resolve eq2907 eq42185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42185
  have eq43359 : y ≠ y ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43358
  have eq43360 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43359
  have eq43372 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq43360
       have r₂ := eq41471
       grind)
    | exact resolve eq43360 eq41471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41471 eq43360
  have eq43387 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26190 eq43372
    | exact resolve eq43372 eq26190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26190 eq43372
  have eq43388 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43387
  have eq43417 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq197 x x
       have i₂ := eq43388
       grind)
    | exact superpose eq43388 eq197
    | exact resolve eq197 eq43388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43388
  have eq43446 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43417
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43417
    | exact resolve eq43417 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43417
  have eq43459 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ y = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq43446
       grind)
    | exact superpose eq43446 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq43446
       grind)
    | exact resolve eq13 eq43446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43461 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq43446
       grind)
    | exact superpose eq43446 eq12
    | exact resolve eq12 eq43446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43446
  have eq43486 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43461
  have eq44524 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq43486
       grind)
    | exact superpose eq43486 eq40
    | exact resolve eq40 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44545 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44524
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44524
    | exact resolve eq44524 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44524
  have eq44549 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq44545
    | exact resolve eq44545 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44545
  have eq44566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44549 eq41341
    | exact resolve eq41341 eq44549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44549
  have eq44581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq44566
  have eq44591 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq44581
       have r₂ := eq27
       grind)
    | exact resolve eq44581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44581
  have eq44637 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44591 eq41446
    | exact resolve eq41446 eq44591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41446
  have eq44638 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq44591
  have eq44639 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq44637
  have eq44653 : (τ (σ y)) = (k y (τ (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq44639
       have r₂ := eq44638
       grind)
    | exact resolve eq44639 eq44638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44638 eq44639
  have eq44664 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq44653
    | exact resolve eq44653 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44653
  have eq44669 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq43459 y
       grind)
    | (have r₁ := eq44664
       have r₂ := eq43459 x
       grind)
    | (have r₁ := eq44664
       have r₂ := eq43459 y
       grind)
    | exact resolve eq44664 eq43459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43459 eq44664
  have eq44708 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43486
       have i₂ := eq44669
       grind)
    | exact superpose eq44669 eq43486
    | exact resolve eq43486 eq44669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43486
  have eq44710 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq44669
       grind)
    | exact superpose eq44669 eq40
    | exact resolve eq40 eq44669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44669
  have eq44725 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq44708
  have eq44752 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44710
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44710
    | exact resolve eq44710 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44710
  have eq45167 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44725 eq27
    | exact resolve eq27 eq44725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45168 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq44725 eq176
    | exact resolve eq176 eq44725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45245 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44752 eq41341
    | exact resolve eq41341 eq44752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41341 eq44752
  have eq45264 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq45245
  have eq45296 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45264 eq27
    | exact resolve eq27 eq45264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45264
  have eq46436 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq45168
    | (have j0 := eq45168 (σ y)
       grind)
    | exact resolve eq45168 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45168
  have eq46501 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44725 eq46436
    | exact resolve eq46436 eq44725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46436
  have eq46504 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq46501
    | exact resolve eq46501 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46501
  have eq46506 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44725 eq46504
    | exact resolve eq46504 eq44725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46504
  have eq46540 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq46506 eq174
    | exact resolve eq174 eq46506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq46543 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq46506 eq12
    | exact resolve eq12 eq46506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46506
  have eq46568 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq46543
  have eq46784 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq46568 eq115
    | exact resolve eq115 eq46568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq46805 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq46568 eq25642
    | exact resolve eq25642 eq46568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25642 eq46568
  have eq46842 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq46805
  have eq46885 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq46842
       have r₂ := eq45167
       grind)
    | exact resolve eq46842 eq45167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46842
  have eq46896 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq46784
    | exact resolve eq46784 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46784
  have eq46919 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq46885
       have r₂ := eq26222
       grind)
    | exact resolve eq46885 eq26222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46885
  have eq47484 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq197 x x
       have i₂ := eq46919
       grind)
    | exact superpose eq46919 eq197
    | exact resolve eq197 eq46919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46919
  have eq47514 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47484
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47484
    | exact resolve eq47484 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47484
  have eq48472 : x ≠ x ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2907 y y
       have i₂ := eq46896
       grind)
    | exact superpose eq46896 eq2907
    | (have j0 := eq2907 y y
       grind)
    | exact resolve eq2907 eq46896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46896
  have eq48473 : x ≠ x ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq48472
  have eq48474 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq48473
  have eq48519 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47514 eq48474
    | exact resolve eq48474 eq47514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48474
  have eq48520 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq48519
  have eq48554 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47514 eq48520
    | exact resolve eq48520 eq47514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47514 eq48520
  have eq48555 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq48554
  have eq48568 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48555 eq31
    | exact resolve eq31 eq48555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48585 : (k y x) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48555 eq114
    | exact resolve eq114 eq48555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq48769 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48555 eq46540
    | exact resolve eq46540 eq48555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46540 eq48555
  have eq48770 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq48769
  have eq48907 : (k x x) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq48585
    | exact resolve eq48585 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq48585
  have eq48924 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq48568
    | exact resolve eq48568 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq48568
  have eq48944 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36999 eq48907
    | exact resolve eq48907 eq36999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36999 eq48907
  have eq48958 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq48924
       grind)
    | exact superpose eq48924 eq24
    | exact resolve eq24 eq48924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49338 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq48958
    | exact resolve eq48958 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48958
  have eq49568 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq49338 eq45296
    | (have r₁ := eq45296
       have r₂ := eq49338
       grind)
    | exact resolve eq45296 eq49338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45296 eq49338
  have eq49577 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq49568
  have eq49578 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq49577
  have eq49631 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44725 eq49578
    | exact resolve eq49578 eq44725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44725 eq49578
  have eq49632 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq49631
  have eq49769 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49632 eq27
    | exact resolve eq27 eq49632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49770 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49632 eq176
    | exact resolve eq176 eq49632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq49955 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48770 eq26324
    | exact resolve eq26324 eq48770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26324 eq48770
  have eq49988 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq49955
  have eq50021 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq49988
       have r₂ := eq45167
       grind)
    | exact resolve eq49988 eq45167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45167 eq49988
  have eq50047 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq50021
       have r₂ := eq26222
       grind)
    | exact resolve eq50021 eq26222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26222 eq50021
  have eq50980 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq197 x x
       have i₂ := eq50047
       grind)
    | exact superpose eq50047 eq197
    | exact resolve eq197 eq50047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq50047
  have eq51011 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50980
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50980
    | exact resolve eq50980 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50980
  have eq51036 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq51011
       grind)
    | exact superpose eq51011 eq12
    | exact resolve eq12 eq51011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51043 : y = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq725 y y
       have i₂ := eq51011
       grind)
    | exact superpose eq51011 eq725
    | exact resolve eq725 eq51011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq51047 : (M.op x y) ≠ (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq774 y y
       have i₂ := eq51011
       grind)
    | exact superpose eq51011 eq774
    | exact resolve eq774 eq51011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774 eq51011
  have eq51063 : y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (M.op x y) := by grind
  clear eq51036
  have eq51068 : (M.op x y) ≠ (M.op y (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq51047
       have r₂ := eq13 y (M.op x y)
       grind)
    | exact resolve eq51047 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51047
  have eq51069 : (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq51043
       have r₂ := eq13 y (M.op x y)
       grind)
    | exact resolve eq51043 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51043
  have eq51070 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq48924 eq51063
    | exact resolve eq51063 eq48924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48924 eq51063
  have eq51077 : (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq51069
       have r₂ := eq51068
       grind)
    | exact resolve eq51069 eq51068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51068 eq51069
  have eq51334 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51077 eq36
    | exact resolve eq36 eq51077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq51077
  have eq51350 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq51334
    | exact resolve eq51334 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51334
  have eq54473 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48944
       have i₂ := eq51070
       grind)
    | exact superpose eq51070 eq48944
    | exact resolve eq48944 eq51070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48944 eq51070
  have eq54491 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq54473
  have eq54513 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq54491
       grind)
    | exact superpose eq54491 eq24
    | exact resolve eq24 eq54491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54491
  have eq54807 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq54513
    | exact resolve eq54513 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54513
  have eq54999 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54807 eq49769
    | exact resolve eq49769 eq54807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49769
  have eq55001 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54807 eq51350
    | exact resolve eq51350 eq54807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51350 eq54807
  have eq55006 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq55001
  have eq55008 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq54999
  have eq55687 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55006 eq2907
    | (have j0 := eq2907 (σ y) (σ y)
       grind)
    | exact resolve eq2907 eq55006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2907 eq55006
  have eq55688 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq55687
  have eq55689 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq55688
  have eq57157 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq49770
    | (have j0 := eq49770 (σ y)
       grind)
    | exact resolve eq49770 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49770
  have eq57229 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49632 eq57157
    | exact resolve eq57157 eq49632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57157
  have eq57231 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq57229
    | exact resolve eq57229 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57229
  have eq57232 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49632 eq57231
    | exact resolve eq57231 eq49632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49632 eq57231
  have eq57266 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57232 eq55689
    | exact resolve eq55689 eq57232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55689 eq57232
  have eq57307 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq57266
  have eq57326 : x = (M.op x y) := by
    first
    | (have r₁ := eq57307
       have r₂ := eq55008
       grind)
    | exact resolve eq57307 eq55008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55008 eq57307
  have eq57336 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq57326
       grind)
    | exact superpose eq57326 eq18
    | exact resolve eq18 eq57326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq57337 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq57326
       grind)
    | exact superpose eq57326 eq22
    | exact resolve eq22 eq57326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq57326
  have eq57465 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq57337 eq20
    | exact resolve eq20 eq57337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58073 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq57336 eq175
    | exact resolve eq175 eq57336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq58134 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq57336 eq58073
    | exact resolve eq58073 eq57336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57336 eq58073
  have eq58155 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq58134
       grind)
    | exact superpose eq58134 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq58134
       grind)
    | exact resolve eq13 eq58134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58157 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq58134
       grind)
    | exact superpose eq58134 eq12
    | exact resolve eq12 eq58134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58186 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq58157
  have eq58694 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq58186
       grind)
    | exact superpose eq58186 eq40
    | exact resolve eq40 eq58186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq58720 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58694
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58694
    | exact resolve eq58694 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58694
  have eq58728 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq58720
    | exact resolve eq58720 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58720
  have eq58734 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57465 eq58728
    | exact resolve eq58728 eq57465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58728
  have eq58806 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58734 eq811
    | (have j0 := eq811 (σ y)
       grind)
    | exact resolve eq811 eq58734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq58734
  have eq58851 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq58806
    | exact resolve eq58806 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58806
  have eq62679 : y = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58851 eq288
    | exact resolve eq288 eq58851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq58851
  have eq62735 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq62679
    | exact resolve eq62679 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq62679
  have eq62742 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq58155 y
       grind)
    | (have r₁ := eq62735
       have r₂ := eq58155 y
       grind)
    | exact resolve eq62735 eq58155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58155 eq62735
  have eq62792 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq58186
       have i₂ := eq62742
       grind)
    | exact superpose eq62742 eq58186
    | exact resolve eq58186 eq62742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58186 eq62742
  have eq62810 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq62792
  have eq62849 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq62810 eq27
    | exact resolve eq27 eq62810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62810
  have eq62888 : y = (M.op x y) := by
    first
    | (have r₁ := eq62849
       have r₂ := eq57465
       grind)
    | exact resolve eq62849 eq57465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62849
  have eq62894 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq62888
       grind)
    | exact superpose eq62888 eq24
    | exact resolve eq24 eq62888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq62898 : (σ y) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq183
       have i₂ := eq62888
       grind)
    | exact superpose eq62888 eq183
    | exact resolve eq183 eq62888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq63069 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq58134
       have i₂ := eq62888
       grind)
    | exact superpose eq62888 eq58134
    | exact resolve eq58134 eq62888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58134 eq62888
  have eq63108 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq63069 eq62898
    | exact resolve eq62898 eq63069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62898 eq63069
  have eq63111 : (σ x) = (σ y) := by
    first
    | exact superpose eq57337 eq62894
    | exact resolve eq62894 eq57337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57337 eq62894
  have eq63125 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq63108
    | exact resolve eq63108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq63108
  have eq63137 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq63111 eq63125
    | exact resolve eq63125 eq63111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63125
  have eq63142 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq57465 eq63137
    | exact resolve eq63137 eq57465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63137
  have eq63143 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63111 eq26
    | exact resolve eq26 eq63111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq63111
  have eq63820 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq63143 eq12
    | exact resolve eq12 eq63143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63143
  have eq63852 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq63820
  have eq63858 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63142 eq63852
    | exact resolve eq63852 eq63142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63142 eq63852
  have eq63859 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq63858
  have eq63885 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq63859 eq27
    | exact resolve eq27 eq63859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq63859
  have eq63936 : False := by grind
  exact eq63936

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_y_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X0) X1
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (k (M.op X0 X0) X0) X0) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq21 X0 X0
       grind)
    | exact superpose eq21 eq31
    | exact resolve eq31 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq80 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq100 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq255 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq16
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (k (σ (k X0 X0)) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 (σ x)
       have i₂ := eq78 x x
       grind)
    | exact superpose eq78 eq34
    | (have j1 := eq78 X0 X0
       grind)
    | exact resolve eq34 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq266 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq267 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq270 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq271 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (k (σ (k X0 X0)) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq277 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq270 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq270
    | (have j0 := eq270 X0
       grind)
    | exact resolve eq270 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq278 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k (k X0 X0) X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq271
    | (have j0 := eq271 X0
       grind)
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq1008 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1045 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1008 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1008
    | (have j0 := eq1008 X0 X1
       grind)
    | exact resolve eq1008 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1250 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (k (τ X0) (τ X0)) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq278 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq1274 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (k (σ (k (τ X0) (τ X0))) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1250 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq1250
    | (have j0 := eq1250 X0
       grind)
    | exact resolve eq1250 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq1281 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (k (σ (τ X0)) X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1274 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1274
    | (have j0 := eq1274 X0
       grind)
    | exact resolve eq1274 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1286 : ∀ X0 : G, (k X0 X0) = (M.op (k (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1281 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1281
    | (have j0 := eq1281 X0
       grind)
    | exact resolve eq1281 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1297 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (k X0 X0) X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (k (k X0 X0) X0)
       have i₂ := eq1286 X0
       grind)
    | exact superpose eq1286 eq9
    | (have j1 := eq1286 X0
       grind)
    | exact resolve eq9 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1355 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq267 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq267
    | (have j0 := eq267 (σ X1) (σ X0)
       grind)
    | exact resolve eq267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq1497 : ∀ X0 : G, (σ (k (τ (k X0 X0)) (τ X0))) = (M.op (σ (τ (k X0 X0))) (σ (τ (k X0 X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq277 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq277
    | (have j0 := eq277 (τ X0)
       grind)
    | exact resolve eq277 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq1542 : ∀ X0 : G, (σ (k (τ (k X0 X0)) (τ X0))) = (M.op (k X0 X0) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1497 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1497
    | (have j0 := eq1497 X0
       grind)
    | exact resolve eq1497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1549 : ∀ X0 : G, (k (σ (τ (k X0 X0))) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1542 X0
       have i₂ := eq19 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq19 eq1542
    | (have j0 := eq1542 X0
       grind)
    | exact resolve eq1542 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1553 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1549 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1549
    | (have j0 := eq1549 X0
       grind)
    | exact resolve eq1549 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1556 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1553 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1553
    | (have j0 := eq1553 X0
       grind)
    | exact resolve eq1553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1562 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1297 X0 (k X0 X0)
       have i₂ := eq1556 X0
       grind)
    | exact superpose eq1556 eq1297
    | (have j0 := eq1297 X0 x
       have j1 := eq1556 X0
       grind)
    | exact resolve eq1297 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1588 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1562 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq1599 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1286 X0
       have i₂ := eq1588 X0
       grind)
    | exact superpose eq1588 eq1286
    | (have j0 := eq1286 X0
       have j1 := eq1588 X0
       grind)
    | exact resolve eq1286 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286 eq1588
  have eq1615 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq1769 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1297 X0 X0
       have i₂ := eq1615 X0
       grind)
    | exact superpose eq1615 eq1297
    | (have j0 := eq1297 X0 x
       have j1 := eq1615 X0
       grind)
    | exact resolve eq1297 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1787 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1769
  have eq1795 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1615 X0
       have i₂ := eq1787 X0
       grind)
    | exact superpose eq1787 eq1615
    | (have j0 := eq1615 X0
       have j1 := eq1787 X0
       grind)
    | exact resolve eq1615 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615 eq1787
  have eq1813 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1795 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1820 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq255
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq255
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq255 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1821 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq1820
  have eq1845 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1813 (σ X0)
       grind)
    | exact superpose eq1813 eq15
    | (have j1 := eq1813 (σ X0)
       grind)
    | exact resolve eq15 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq2241 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq100 (σ X0)
       have i₂ := eq1845 X0
       grind)
    | exact superpose eq1845 eq100
    | (have j1 := eq1845 X0
       grind)
    | exact resolve eq100 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq2263 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2241 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2241
    | (have j0 := eq2241 X0
       grind)
    | exact resolve eq2241 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241
  have eq2264 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2263 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq2366 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2264 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2264
    | exact resolve eq2264 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2393 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0) (σ X0)
       have i₂ := eq2264 X0
       grind)
    | exact superpose eq2264 eq21
    | exact resolve eq21 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2429 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq2366 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq2366
    | exact resolve eq2366 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2440 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2429 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2429
    | exact resolve eq2429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429
  have eq2809 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2393 X0
       have i₂ := eq2440 X0
       grind)
    | exact superpose eq2440 eq2393
    | exact resolve eq2393 eq2440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393
  have eq3059 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq21 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq2809 X0
       grind)
    | exact superpose eq2809 eq21
    | exact resolve eq21 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2809
  have eq3084 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3059 X0
       have i₂ := eq2264 (M.op X0 X0)
       grind)
    | exact superpose eq2264 eq3059
    | exact resolve eq3059 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3059
  have eq3106 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3084 X0
       have i₂ := eq2440 (M.op X0 X0)
       grind)
    | exact superpose eq2440 eq3084
    | exact resolve eq3084 eq2440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084
  have eq3122 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq3106
  have eq3133 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3122 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq3122
    | exact resolve eq3122 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq3122
  have eq35600 : x ≠ x ∨ x = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1821
       grind)
    | exact superpose eq1821 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1821
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1821
       grind)
    | exact resolve eq13 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq35628 : x ≠ x ∨ x = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35600
  have eq35629 : x = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35628
  have eq35657 : (σ y) = (σ (k x x)) ∨ x = (k y x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35629
       have i₂ := eq2264 x
       grind)
    | exact superpose eq2264 eq35629
    | exact resolve eq35629 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35629
  have eq35686 : x = (k y x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35657
       have i₂ := eq2440 x
       grind)
    | exact superpose eq2440 eq35657
    | exact resolve eq35657 eq2440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35657
  have eq84437 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1355 (τ X0) (τ X1)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq1355
    | (have j0 := eq1355 (τ X0) (τ X1)
       grind)
    | exact resolve eq1355 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1355
  have eq84540 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq84437 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq84437
    | (have j0 := eq84437 X0 X1
       grind)
    | exact resolve eq84437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84437
  have eq84595 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq84540 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq84540
    | (have j0 := eq84540 X0 X1
       grind)
    | exact resolve eq84540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84540
  have eq84648 : ∀ X0 X1 : G, (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq84595 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84595
    | (have j0 := eq84595 X0 X1
       grind)
    | exact resolve eq84595 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84595
  have eq84695 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq84648 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84648
    | (have j0 := eq84648 X0 X1
       grind)
    | exact resolve eq84648 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84648
  have eq84734 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84695 X0 X1
       have i₂ := eq2264 (σ (τ X1))
       grind)
    | exact superpose eq2264 eq84695
    | (have j0 := eq84695 X0 X1
       grind)
    | exact resolve eq84695 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84695
  have eq84768 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84734 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq84734
    | (have j0 := eq84734 X0 X1
       grind)
    | exact resolve eq84734 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84734
  have eq84798 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84768 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq84768
    | (have j0 := eq84768 X0 X1
       grind)
    | exact resolve eq84768 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq84768
  have eq84821 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84798 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq84798
    | (have j0 := eq84798 X0 X1
       grind)
    | exact resolve eq84798 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84798
  have eq84839 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84821 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84821
    | (have j0 := eq84821 X0 X1
       grind)
    | exact resolve eq84821 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84821
  have eq84855 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84839 X0 X1
       have i₂ := eq2440 X1
       grind)
    | exact superpose eq2440 eq84839
    | (have j0 := eq84839 X0 X1
       grind)
    | exact resolve eq84839 eq2440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84839
  have eq554466 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq84855 y x
       have i₂ := eq35686
       grind)
    | exact superpose eq35686 eq84855
    | (have j0 := eq84855 y x
       grind)
    | exact resolve eq84855 eq35686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35686 eq84855
  have eq554518 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq554466
  have eq554519 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq554518
  have eq554561 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq554519
       grind)
    | exact superpose eq554519 eq16
    | exact resolve eq16 eq554519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554586 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq554519
       grind)
    | exact superpose eq554519 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq554519
       grind)
    | exact resolve eq13 eq554519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554519
  have eq554658 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq554586
  have eq554691 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq554658
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq554658
    | exact resolve eq554658 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554658
  have eq554738 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq554691
       have i₂ := eq2264 x
       grind)
    | exact superpose eq2264 eq554691
    | exact resolve eq554691 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264 eq554691
  have eq554763 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq554738
       have i₂ := eq2440 x
       grind)
    | exact superpose eq2440 eq554738
    | exact resolve eq554738 eq2440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2440 eq554738
  have eq554764 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq554763
  have eq556210 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1045 y x
       have i₂ := eq554764
       grind)
    | exact superpose eq554764 eq1045
    | (have j0 := eq1045 y x
       grind)
    | exact resolve eq1045 eq554764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq554764
  have eq556553 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq556210
  have eq556714 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq556553
       have r₂ := eq554561
       grind)
    | exact resolve eq556553 eq554561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556553
  have eq558965 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq554561
       have i₂ := eq556714
       grind)
    | exact superpose eq556714 eq554561
    | exact resolve eq554561 eq556714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554561 eq556714
  have eq559041 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq558965
  have eq559042 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq559041
  have eq561158 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq559042
       grind)
    | exact superpose eq559042 eq10
    | exact resolve eq10 eq559042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559042
  have eq561703 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq561158
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq561158
    | exact resolve eq561158 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561158
  have eq561704 : y = (M.op x x) := by grind
  clear eq561703
  have eq561963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3133 x
       have i₂ := eq561704
       grind)
    | exact superpose eq561704 eq3133
    | exact resolve eq3133 eq561704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133 eq561704
  have eq562311 : False := by grind
  exact eq562311

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq48
    | exact resolve eq48 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq53
    | exact resolve eq53 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq53
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) (σ X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq20
    | exact resolve eq20 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | (have j0 := eq87 X1 X1
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq134 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq119
    | (have j0 := eq119 X0 X1
       grind)
    | exact resolve eq119 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq140 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq96 X1 X0
       grind)
    | (have r₁ := eq134 X0 X0
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq134 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq910 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140
    | exact resolve eq140 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq140 (σ X1) X0
       grind)
    | exact superpose eq140 eq15
    | (have j1 := eq140 (σ X1) X0
       grind)
    | exact resolve eq15 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq941 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq910 X0 X1
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq910
    | (have j0 := eq910 X0 X1
       grind)
    | exact resolve eq910 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq910
  have eq966 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq941 X0 (τ X1)
       grind)
    | exact superpose eq941 eq17
    | (have j1 := eq941 X0 (τ X1)
       grind)
    | exact resolve eq17 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq941
  have eq4232 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq966 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq966
    | exact resolve eq966 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq4321 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4232 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4232
    | (have j0 := eq4232 X0 X1
       grind)
    | exact resolve eq4232 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232
  have eq9199 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq923 x y
       grind)
    | exact superpose eq923 eq16
    | (have j1 := eq923 x y
       grind)
    | exact resolve eq16 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9261 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq923 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq9379 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9199
       have i₂ := eq4321 y x
       grind)
    | exact superpose eq4321 eq9199
    | (have j1 := eq4321 y x
       grind)
    | (have r₁ := eq9199
       have r₂ := eq4321 y x
       grind)
    | exact resolve eq9199 eq4321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321 eq9199
  have eq9380 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq9379
  have eq9384 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq9380
       grind)
    | exact superpose eq9380 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9380
       grind)
    | exact resolve eq13 eq9380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9380
  have eq9400 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq9384
  have eq43821 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9261 x y
       have i₂ := eq9400
       grind)
    | exact superpose eq9400 eq9261
    | (have j0 := eq9261 x y
       grind)
    | exact resolve eq9261 eq9400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9261 eq9400
  have eq43832 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq43821
  have eq43833 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq43832
  have eq44407 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43833
       grind)
    | exact superpose eq43833 eq16
    | exact resolve eq16 eq43833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44414 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ (M.op x x)) X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq43833
       grind)
    | exact superpose eq43833 eq9
    | exact resolve eq9 eq43833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44416 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 (σ x) (σ y)
       have i₂ := eq43833
       grind)
    | exact superpose eq43833 eq20
    | exact resolve eq20 eq43833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44470 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44416
       have i₂ := eq93 x
       grind)
    | exact superpose eq93 eq44416
    | exact resolve eq44416 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq44416
  have eq44688 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 (σ y) (σ x)
       have i₂ := eq44470
       grind)
    | exact superpose eq44470 eq20
    | exact resolve eq20 eq44470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44470
  have eq45400 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44414 (σ y)
       have i₂ := eq44688
       grind)
    | exact superpose eq44688 eq44414
    | exact resolve eq44414 eq44688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44414
  have eq45462 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq45400
  have eq45474 : (σ (M.op y y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45462
       have i₂ := eq55 y
       grind)
    | exact superpose eq55 eq45462
    | exact resolve eq45462 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq45462
  have eq45485 : (σ (M.op y y)) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45474
       have i₂ := eq43833
       grind)
    | exact superpose eq43833 eq45474
    | exact resolve eq45474 eq43833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45474
  have eq45540 : (σ (M.op y y)) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq45485
  have eq46176 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44688
       have i₂ := eq45540
       grind)
    | exact superpose eq45540 eq44688
    | exact resolve eq44688 eq45540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44688 eq45540
  have eq46233 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq46176
  have eq46278 : (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43833
       have i₂ := eq46233
       grind)
    | exact superpose eq46233 eq43833
    | exact resolve eq43833 eq46233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43833 eq46233
  have eq46335 : (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq46278
  have eq46697 : (M.op y y) = (τ (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq46335
       grind)
    | exact superpose eq46335 eq10
    | exact resolve eq10 eq46335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46335
  have eq46856 : (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq46697
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq46697
    | exact resolve eq46697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46697
  have eq47149 : (M.op x x) = (M.op (M.op x x) y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 y y
       have i₂ := eq46856
       grind)
    | exact superpose eq46856 eq20
    | exact resolve eq20 eq46856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46856
  have eq47195 : (M.op y x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 y x x
       have i₂ := eq47149
       grind)
    | exact superpose eq47149 eq9
    | exact resolve eq9 eq47149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47257 : (M.op x x) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq47195
       have i₂ := eq20 x x
       grind)
    | exact superpose eq20 eq47195
    | exact resolve eq47195 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47195
  have eq47439 : (M.op x y) = (M.op (M.op x x) y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 y x
       have i₂ := eq47257
       grind)
    | exact superpose eq47257 eq20
    | exact resolve eq20 eq47257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq47257
  have eq47477 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq47149
       have i₂ := eq47439
       grind)
    | exact superpose eq47439 eq47149
    | exact resolve eq47149 eq47439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47149 eq47439
  have eq47524 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq47477
  have eq47698 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44407
       have i₂ := eq47524
       grind)
    | exact superpose eq47524 eq44407
    | exact resolve eq44407 eq47524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44407 eq47524
  have eq47742 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq47698
  have eq47743 : x = (M.op x x) := by grind
  clear eq47742
  have eq47745 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq47743
       grind)
    | exact superpose eq47743 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq47743
       grind)
    | exact resolve eq12 eq47743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47748 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq96 x X0
       have i₂ := eq47743
       grind)
    | exact superpose eq47743 eq96
    | (have j0 := eq96 x X0
       grind)
    | exact resolve eq96 eq47743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq47743
  have eq47864 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq47748 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47748
  have eq47865 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq47745 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47745
  have eq49289 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq47864 (σ X0)
       grind)
    | exact superpose eq47864 eq15
    | exact resolve eq15 eq47864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47864
  have eq49379 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq49289 X0
       have i₂ := eq47865 X0
       grind)
    | exact superpose eq47865 eq49289
    | exact resolve eq49289 eq47865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47865 eq49289
  have eq51749 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49379 y
       grind)
    | exact superpose eq49379 eq16
    | (have r₁ := eq16
       have r₂ := eq49379 y
       grind)
    | exact resolve eq16 eq49379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49379
  have eq51932 : False := by grind
  exact eq51932

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation4209 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq819 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq970 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq979 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq962 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq962
    | (have j0 := eq962 X0 X1
       grind)
    | exact resolve eq962 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq4093 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq979 x y
       grind)
    | exact superpose eq979 eq16
    | (have j1 := eq979 x y
       grind)
    | exact resolve eq16 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4114 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq979 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq14726 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq970 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq970
    | exact resolve eq970 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq14844 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14726 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14726
    | (have j0 := eq14726 X0 X1
       grind)
    | exact resolve eq14726 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14726
  have eq27074 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq4093
       have i₂ := eq14844 y x
       grind)
    | exact superpose eq14844 eq4093
    | (have j1 := eq14844 y x
       grind)
    | (have r₁ := eq4093
       have r₂ := eq14844 y x
       grind)
    | (have r₁ := eq4093
       have r₂ := eq14844 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4093
       have r₂ := eq14844 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4093 eq14844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4093 eq14844
  have eq27075 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq27074
  have eq30067 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4114 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq4114
    | (have j0 := eq4114 (τ X1) (τ X0)
       grind)
    | exact resolve eq4114 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq30125 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30067 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq30067
    | (have j0 := eq30067 X0 X1
       grind)
    | exact resolve eq30067 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30067
  have eq30160 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30125 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq30125
    | (have j0 := eq30125 X0 X1
       grind)
    | exact resolve eq30125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30125
  have eq30192 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30160 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30160
    | (have j0 := eq30160 X0 X1
       grind)
    | exact resolve eq30160 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30160
  have eq30218 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30192 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq30192
    | (have j0 := eq30192 X0 X1
       grind)
    | exact resolve eq30192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30192
  have eq30238 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30218 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq30218
    | (have j0 := eq30218 X0 X1
       grind)
    | exact resolve eq30218 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq30218
  have eq30257 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30238 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq30238
    | (have j0 := eq30238 X0 X1
       grind)
    | exact resolve eq30238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30238
  have eq30270 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30257 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30257
    | (have j0 := eq30257 X0 X1
       grind)
    | exact resolve eq30257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30257
  have eq58541 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27075
       grind)
    | exact superpose eq27075 eq16
    | exact resolve eq16 eq27075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27075
  have eq58542 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq58541
       have r₂ := eq22 x
       grind)
    | exact resolve eq58541 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58541
  have eq58544 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq58542
       grind)
    | exact superpose eq58542 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq58542
       grind)
    | exact resolve eq13 eq58542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58542
  have eq58600 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq58544
  have eq73164 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58600
       grind)
    | exact superpose eq58600 eq16
    | exact resolve eq16 eq58600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58600
  have eq73165 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq73164
       have r₂ := eq22 x
       grind)
    | exact resolve eq73164 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73164
  have eq73171 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4114 x y
       have i₂ := eq73165
       grind)
    | exact superpose eq73165 eq4114
    | (have j0 := eq4114 x y
       grind)
    | exact resolve eq4114 eq73165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114 eq73165
  have eq73201 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq73171
  have eq73202 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq73201
  have eq73209 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73202
       grind)
    | exact superpose eq73202 eq16
    | exact resolve eq16 eq73202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73210 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq819 x (σ y)
       have i₂ := eq73202
       grind)
    | exact superpose eq73202 eq819
    | (have j0 := eq819 x (σ y)
       grind)
    | (have r₁ := eq819 x (σ y)
       have r₂ := eq73202
       grind)
    | exact resolve eq819 eq73202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq73202
  have eq73285 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq73210
  have eq73286 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq73285
  have eq73320 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq73286
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq73286
    | exact resolve eq73286 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73286
  have eq73354 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq73320
       grind)
    | exact superpose eq73320 eq10
    | exact resolve eq10 eq73320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73320
  have eq73555 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq73354
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq73354
    | exact resolve eq73354 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73354
  have eq73557 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73555
       grind)
    | exact superpose eq73555 eq16
    | exact resolve eq16 eq73555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73555
  have eq73558 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq73557
       have r₂ := eq22 x
       grind)
    | exact resolve eq73557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73557
  have eq73573 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq73558
       grind)
    | exact superpose eq73558 eq10
    | exact resolve eq10 eq73558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73558
  have eq73779 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq73573
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq73573
    | exact resolve eq73573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73573
  have eq73813 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq30270 y x
       have i₂ := eq73779
       grind)
    | exact superpose eq73779 eq30270
    | (have j0 := eq30270 y x
       grind)
    | (have r₁ := eq30270 y x
       have r₂ := eq73779
       grind)
    | exact resolve eq30270 eq73779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30270 eq73779
  have eq73820 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq73813
  have eq73825 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73820
       grind)
    | exact superpose eq73820 eq16
    | exact resolve eq16 eq73820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73820
  have eq73828 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq73825
       have r₂ := eq22 x
       grind)
    | exact resolve eq73825 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73825
  have eq73829 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq73209
       have i₂ := eq73828
       grind)
    | exact superpose eq73828 eq73209
    | exact resolve eq73209 eq73828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73209
  have eq73894 : (σ x) = (σ y) := by grind
  clear eq73829
  have eq73900 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73894
       grind)
    | exact superpose eq73894 eq16
    | exact resolve eq16 eq73894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73894
  have eq74107 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq73900
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq73900
    | exact resolve eq73900 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq73900
  have eq74109 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq74107
       have i₂ := eq73828
       grind)
    | exact superpose eq73828 eq74107
    | exact resolve eq74107 eq73828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73828 eq74107
  have eq74110 : False := by grind
  exact eq74110

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pyx_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq26
  have eq70 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq70 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq70 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq44
    | exact resolve eq44 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq15
    | exact resolve eq15 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq73
    | exact resolve eq73 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq71 (τ X0)
       grind)
    | exact superpose eq71 eq72
    | exact resolve eq72 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq72
  have eq79 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq156 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq134
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq134
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq134
       have r₂ := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq134 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq157 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq156
  have eq873 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq75 (σ y)
       have i₂ := eq157
       grind)
    | exact superpose eq157 eq75
    | exact resolve eq75 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq889 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq873
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq873
    | exact resolve eq873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq916 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq889
       have i₂ := eq75 (σ x)
       grind)
    | exact superpose eq75 eq889
    | exact resolve eq889 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq917 : (M.op y y) = (M.op x x) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq916
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq916
    | exact resolve eq916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq918 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq917
  have eq935 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq75 (σ y)
       have i₂ := eq918
       grind)
    | exact superpose eq918 eq75
    | exact resolve eq75 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq943 : y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq935
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq935
    | exact resolve eq935 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq944 : (M.op y y) = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq943
  have eq964 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op y (M.op y (M.op X0 (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 y
       have i₂ := eq944
       grind)
    | exact superpose eq944 eq9
    | exact resolve eq9 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74 y
       have i₂ := eq944
       grind)
    | exact superpose eq944 eq74
    | exact resolve eq74 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq987 : y = (M.op y y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq979
       have i₂ := eq74 x
       grind)
    | exact superpose eq74 eq979
    | exact resolve eq979 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1032 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y (M.op y (M.op X0 (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq74 y
       have i₂ := eq964 X0
       grind)
    | exact superpose eq964 eq74
    | (have j1 := eq964 X0
       grind)
    | exact resolve eq74 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 X1 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) ∨ y = (M.op y (M.op y (M.op X1 (M.op x x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq964 X1
       grind)
    | exact superpose eq964 eq12
    | (have j0 := eq12 X0 y
       have j1 := eq964 X1
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq964 X0
       grind)
    | exact resolve eq12 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1036 : ∀ X0 X1 : G, (M.op X0 y) = (k X0 y) ∨ y = (M.op y (M.op y (M.op X1 (M.op x x)))) := by
    intro X0 X1
    first
    | (have j0 := eq1035 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1080 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74 y
       have i₂ := eq987
       grind)
    | exact superpose eq987 eq74
    | exact resolve eq74 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq987
       grind)
    | exact superpose eq987 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq987
       grind)
    | exact resolve eq12 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1084 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1155 : ∀ X0 X1 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ y = (M.op y (M.op y (M.op X1 (M.op x x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1036 X0 X1
       grind)
    | exact superpose eq1036 eq15
    | (have j1 := eq1036 X0 X1
       grind)
    | exact resolve eq15 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1157 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1084 X0
       grind)
    | exact superpose eq1084 eq15
    | exact resolve eq15 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1267 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op y (M.op y (M.op X1 (M.op x x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq1032 X1
       grind)
    | exact superpose eq1032 eq12
    | (have j0 := eq12 X0 (σ y)
       have j1 := eq1032 X1
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq1032 X0
       grind)
    | exact resolve eq12 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1268 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op y (M.op y (M.op X1 (M.op x x)))) := by
    intro X0 X1
    first
    | (have j0 := eq1267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1341 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq1080
       grind)
    | exact superpose eq1080 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq1080
       grind)
    | exact resolve eq12 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq1343 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1632 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ y = (M.op y (M.op y (M.op X0 (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1155 x X0
       grind)
    | exact superpose eq1155 eq16
    | (have j1 := eq1155 X0 X0
       grind)
    | exact resolve eq16 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1636 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 (M.op x x)))) := by
    intro X0
    first
    | (have j0 := eq1632 X0
       have j1 := eq1268 X0 X0
       grind)
    | (have r₁ := eq1632 X0
       have r₂ := eq1268 (σ x) x
       grind)
    | exact resolve eq1632 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268 eq1632
  have eq1804 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1157 x
       grind)
    | exact superpose eq1157 eq16
    | exact resolve eq16 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1809 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq1804
       have r₂ := eq1343 (σ x)
       grind)
    | exact resolve eq1804 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343 eq1804
  have eq1836 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq75 (σ y)
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq75
    | exact resolve eq75 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1838 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1809
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1809
       grind)
    | exact resolve eq13 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq1861 : (M.op y y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1836
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1836
    | exact resolve eq1836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq1863 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq1861
       have i₂ := eq75 (σ x)
       grind)
    | exact superpose eq75 eq1861
    | exact resolve eq1861 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq1864 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1863
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1863
    | exact resolve eq1863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq1939 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1864
       grind)
    | exact superpose eq1864 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1864
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1864
       grind)
    | exact resolve eq13 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2199 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq1939 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq2208 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq2199
       grind)
    | exact superpose eq2199 eq15
    | exact resolve eq15 eq2199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq2218 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2208
       grind)
    | exact superpose eq2208 eq16
    | exact resolve eq16 eq2208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208
  have eq2574 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2218
       have i₂ := eq1838 (σ x)
       grind)
    | exact superpose eq1838 eq2218
    | (have j1 := eq1838 (σ x)
       grind)
    | (have r₁ := eq2218
       have r₂ := eq1838 (σ x)
       grind)
    | exact resolve eq2218 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838 eq2218
  have eq2579 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2574
  have eq2589 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75 (σ x)
       have i₂ := eq2579
       grind)
    | exact superpose eq2579 eq75
    | exact resolve eq75 eq2579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq2579
  have eq2630 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2589
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2589
    | exact resolve eq2589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2589
  have eq2631 : x = (M.op x x) := by grind
  clear eq2630
  have eq2650 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq1636 X0
       have i₂ := eq2631
       grind)
    | exact superpose eq2631 eq1636
    | exact resolve eq1636 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq2717 : x = (M.op y y) := by
    first
    | (have i₁ := eq1864
       have i₂ := eq2631
       grind)
    | exact superpose eq2631 eq1864
    | exact resolve eq1864 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq3653 : y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq2650 x
       have i₂ := eq2631
       grind)
    | exact superpose eq2631 eq2650
    | exact resolve eq2650 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq3686 : y = (M.op y y) := by
    first
    | (have i₁ := eq2650 y
       have i₂ := eq3653
       grind)
    | exact superpose eq3653 eq2650
    | exact resolve eq2650 eq3653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650 eq3653
  have eq3750 : x = y := by
    first
    | (have i₁ := eq3686
       have i₂ := eq2717
       grind)
    | exact superpose eq2717 eq3686
    | exact resolve eq3686 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717 eq3686
  have eq3753 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3750
       grind)
    | exact superpose eq3750 eq16
    | exact resolve eq16 eq3750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3750
  have eq4621 : False := by grind
  exact eq4621
