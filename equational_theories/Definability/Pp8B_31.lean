import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq30 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq30 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq32 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq32 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq32 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq37
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq123 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq127 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq123 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | (have r₁ := eq123 X0 X1
       have r₂ := eq44 X0 X1
       grind)
    | (have r₁ := eq123 X0 X0
       have r₂ := eq44 X0 X0
       grind)
    | exact resolve eq123 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq123
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq127 (σ X0) (σ X1)
       grind)
    | exact superpose eq127 eq15
    | exact resolve eq15 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq127 X0 X1
       grind)
    | exact superpose eq127 eq235
    | exact resolve eq235 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq235
  have eq244 : False := by grind
  exact eq244

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X0 X3)) ≠ X0 ∨ (M.op X0 X3) = (M.op (M.op X0 X3) (M.op (M.op X1 X2) X0)) ∨ (M.op (M.op X0 X3) (M.op X0 X3)) = (k (M.op (M.op X1 X2) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op (M.op X1 X2) X0) (M.op X0 X3)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X1 X2) X0) (M.op X0 X3)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X1 X2) = X1 ∨ (M.op X0 X1) = (k X2 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X1 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq11 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) ∨ (M.op X0 X1) = (k X2 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X2) (M.op X1 X2))
       have i₂ := eq14 (M.op X1 X2) X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq111 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq118 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq43
    | exact resolve eq43 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq119 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq115 y
       grind)
    | exact superpose eq115 eq76
    | exact resolve eq76 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq115 sF3
       grind)
    | exact superpose eq115 eq119
    | exact resolve eq119 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq115 sF2
       grind)
    | exact superpose eq115 eq118
    | exact resolve eq118 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq134 : (σ (k (M.op x y) (k y y))) = (k (σ (M.op x y)) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq37 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq37
    | exact resolve eq37 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq136 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq115 sF1
       grind)
    | exact superpose eq115 eq138
    | exact resolve eq138 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq140 : (σ (k (M.op x y) (k y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq134
       have i₂ := eq115 sF3
       grind)
    | exact superpose eq115 eq134
    | exact resolve eq134 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq115 sF0
       grind)
    | exact superpose eq115 eq139
    | exact resolve eq139 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq143 : (k (σ (M.op x y)) (M.op (σ y) (σ y))) = (σ (k (M.op x y) (M.op y y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq115 y
       grind)
    | exact superpose eq115 eq140
    | exact resolve eq140 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq150 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq160 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq142 eq35
    | exact resolve eq35 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq252 eq14
    | exact resolve eq14 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq253 eq14
    | exact resolve eq14 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq347 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (M.op (M.op x y) (M.op X0 x)) = (k (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq361 eq13
    | (have j0 := eq13 (M.op x y) (M.op X0 x)
       grind)
    | exact resolve eq13 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq551 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq1056 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq493 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq493
    | (have j0 := eq493 X0 x
       grind)
    | exact resolve eq493 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1222 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq551 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq551
    | (have j0 := eq551 x X0
       grind)
    | exact resolve eq551 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1991 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq109 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1992 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1991 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq1999 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1992 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq1992 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1992 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq2293 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X0)) ∨ (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f2293_14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X0 X3)) ≠ X0 ∨ (M.op X0 X3) = (M.op (M.op X0 X3) (M.op (M.op X1 X2) X0)) ∨ (M.op (M.op X0 X3) (M.op X0 X3)) = (k (M.op (M.op X1 X2) X0) (M.op X0 X3)) := by
      intro X0 X1 X2 X3
      grind
    have f2293_15 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = X1 := by
      intro X0 X1 X2
      grind
    have f2293_25 : (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op (M.op X1 X2) X0)) := by grind
    have f2293_26 : X0 ≠ (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) := by grind
    have f2293_159 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X0)) ∨ (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 := by
      intro X0 X1 X2
      first
      | (have i₁ := f2293_14 X2 X1 X2 X2
         have i₂ := f2293_15 X2 X2 X2
         grind)
      | exact superpose f2293_15 f2293_14
      | (have j0 := f2293_14 X0 X1 X2 X0
         grind)
      | (have r₁ := f2293_14 X2 X1 X2 X2
         have r₂ := f2293_15 X2 X2 X2
         grind)
      | exact resolve f2293_14 f2293_15
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2293_163 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X0)) := by
      intro X0 X1 X2
      first
      | (have j0 := f2293_159 X0 X1 X2
         grind)
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2293_1048 : X0 ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X0)) := by
      first
      | (have i₁ := f2293_26
         have i₂ := f2293_163 X0 X1 X2
         grind)
      | exact superpose f2293_163 f2293_26
      | (have j1 := f2293_163 X0 X1 X2
         grind)
      | (have r₁ := f2293_26
         have r₂ := f2293_163 X0 X1 X2
         grind)
      | exact resolve f2293_26 f2293_163
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2293_1058 : (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X0)) := by grind
    have f2293_1064 : False := by
      first
      | (have r₁ := f2293_1058
         have r₂ := f2293_25
         grind)
      | exact resolve f2293_1058 f2293_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f2293_1064
  have eq2297 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op X0 X1) (M.op x y))) ∨ (M.op x y) = (k (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq108
    | (have j0 := eq108 (M.op x y) X0 X1 (M.op x y)
       grind)
    | (have r₁ := eq108 (M.op x y) X1 x (M.op x y)
       have r₂ := eq50 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq108 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq2304 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op X0 X1) (M.op x y))) ∨ (M.op x y) = (k (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have j0 := eq2297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq2307 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X0)) ∨ (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2293 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2293
  have eq2513 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1 X0
       have i₂ := eq53 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq110
    | (have j0 := eq110 X0 X1 X0
       grind)
    | (have r₁ := eq110 X0 x X0
       have r₂ := eq53 X0 x (M.op X0 x)
       grind)
    | exact resolve eq110 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq2540 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2513 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513
  have eq2580 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq1999 X1 (τ X0)
       grind)
    | exact superpose eq1999 eq34
    | (have j1 := eq1999 X1 (τ X0)
       grind)
    | exact resolve eq34 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq2589 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 X0
       have i₂ := eq1999 (τ X1) X0
       grind)
    | exact superpose eq1999 eq38
    | (have j1 := eq1999 (τ X1) X0
       grind)
    | exact resolve eq38 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq2599 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1999 y x
       grind)
    | exact superpose eq1999 eq44
    | (have j1 := eq1999 y x
       grind)
    | exact resolve eq44 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2623 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2599
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2599
    | exact resolve eq2599 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2599
  have eq2635 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq2623
    | exact resolve eq2623 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623
  have eq2685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2635
       have i₂ := eq1999 sF3 sF2
       grind)
    | exact superpose eq1999 eq2635
    | (have j1 := eq1999 y x
       grind)
    | exact resolve eq2635 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635
  have eq2692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2685
    | exact resolve eq2685 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq2694 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq2692
       have r₂ := eq27
       grind)
    | exact resolve eq2692 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692
  have eq2711 : (τ (σ x)) = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq2694 eq60
    | exact resolve eq60 eq2694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694
  have eq2714 : x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq2711
    | exact resolve eq2711 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2715 : x = (k x y) := by grind
  clear eq2714
  have eq2718 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2715
       grind)
    | exact superpose eq2715 eq44
    | exact resolve eq44 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq2719 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2718
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2718
    | exact resolve eq2718 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718
  have eq18202 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq252 eq2304
    | exact resolve eq2304 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18242 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (M.op (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq2304 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))
       have j1 := eq2304 X0 X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))
       have r₂ := eq2304 X0 X1
       grind)
    | exact resolve eq13 eq2304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304
  have eq18281 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (M.op (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have j0 := eq18242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18242
  have eq18294 : ∀ X0 X1 : G, (M.op x y) = (k (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq18281 X1 x
       have i₂ := eq14 sF0 X1 x sF0
       grind)
    | exact superpose eq14 eq18281
    | (have j0 := eq18281 X0 X1
       grind)
    | exact resolve eq18281 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18281
  have eq18295 : ∀ X0 X1 : G, (M.op x y) = (k (M.op (M.op X0 X1) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have j0 := eq18294 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18294
  have eq18571 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op (M.op X1 X2) X0) (M.op X0 X0)) = (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) ∨ (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 X2) X0) (M.op X0 X0)
       have i₂ := eq2307 X0 X1 X2
       grind)
    | exact superpose eq2307 eq13
    | (have j0 := eq13 (M.op (M.op X1 X2) X0) (M.op X0 X0)
       have j1 := eq2307 X0 X1 X2
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X2) X0) (M.op X0 X0)
       have r₂ := eq2307 X0 X1 X2
       grind)
    | exact resolve eq13 eq2307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq18611 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X0)) = (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) ∨ (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq18571 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18571
  have eq18628 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 ∨ (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18611 X0 X1 X2
       have i₂ := eq14 X0 X1 X2 X0
       grind)
    | exact superpose eq14 eq18611
    | (have j0 := eq18611 X0 X1 X2
       grind)
    | exact resolve eq18611 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18611
  have eq18629 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq18628 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18628
  have eq36176 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq2540 X0 X1
       grind)
    | exact superpose eq2540 eq13
    | (have j0 := eq13 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have j1 := eq2540 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have r₂ := eq2540 X0 X1
       grind)
    | exact resolve eq13 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq36273 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq36176 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36176
  have eq36317 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36273 X0 X1
       have i₂ := eq53 X0 X1 (M.op X0 X1)
       grind)
    | (have i₁ := eq36273 X0 X1
       have i₂ := eq53 X0 (M.op (M.op X0 X1) (M.op X0 X1)) x
       grind)
    | exact superpose eq53 eq36273
    | (have j0 := eq36273 X0 X1
       grind)
    | exact resolve eq36273 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq36273
  have eq36318 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq36317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36317
  have eq221944 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ y))) = (σ (M.op X0 (k x y))) ∨ (k X0 (k x y)) = X0 := by
    intro X0
    first
    | exact superpose eq60 eq2589
    | exact resolve eq2589 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2589
  have eq222201 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ y))) = (σ (M.op X0 x)) ∨ (k X0 (k x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq221944 X0
       have i₂ := eq2715
       grind)
    | exact superpose eq2715 eq221944
    | (have j0 := eq221944 X0
       grind)
    | exact resolve eq221944 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221944
  have eq222253 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ (k X0 (k x y)) = X0 := by
    intro X0
    first
    | exact superpose eq2719 eq222201
    | (have j0 := eq222201 X0
       grind)
    | exact resolve eq222201 eq2719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222201
  have eq222285 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (k X0 (k x y)) = X0 := by
    intro X0
    first
    | exact superpose eq39 eq222253
    | (have j0 := eq222253 X0
       grind)
    | exact resolve eq222253 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq222253
  have eq222307 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq222285 X0
       have i₂ := eq2715
       grind)
    | exact superpose eq2715 eq222285
    | (have j0 := eq222285 X0
       grind)
    | exact resolve eq222285 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222285
  have eq222334 : ∀ X0 : G, (σ (τ (k X0 (σ x)))) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq222307 (τ X0)
       have i₂ := eq1056 X0
       grind)
    | exact superpose eq1056 eq222307
    | exact resolve eq222307 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq222307
  have eq222633 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq222334 X0
       have i₂ := eq15 (k X0 sF2)
       grind)
    | exact superpose eq15 eq222334
    | (have j0 := eq222334 X0
       grind)
    | exact resolve eq222334 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222334
  have eq223382 : ∀ X0 : G, (τ (k X0 (σ x))) = (M.op (τ X0) x) ∨ (τ X0) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) x)
       have i₂ := eq222633 X0
       grind)
    | exact superpose eq222633 eq16
    | (have j1 := eq222633 X0
       grind)
    | exact resolve eq16 eq222633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222633
  have eq223679 : ∀ X0 : G, x = (M.op (τ (k X0 (σ x))) (M.op x y)) ∨ (τ X0) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq361 (τ X0)
       have i₂ := eq223382 X0
       grind)
    | exact superpose eq223382 eq361
    | (have j1 := eq223382 X0
       grind)
    | exact resolve eq361 eq223382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223382
  have eq224250 : ∀ X0 : G, x = (M.op (k X0 (τ (σ x))) (M.op x y)) ∨ (τ (σ X0)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq223679 (σ X0)
       have i₂ := eq551 X0 sF2
       grind)
    | exact superpose eq551 eq223679
    | exact resolve eq223679 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq224266 : x = (M.op (k (M.op x y) x) (M.op x y)) ∨ (τ (σ (M.op x y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq150 eq223679
    | exact resolve eq223679 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq223679
  have eq224518 : x = (M.op (k (M.op x y) x) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq224266
    | exact resolve eq224266 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224266
  have eq224528 : ∀ X0 : G, x = (M.op (k X0 x) (M.op x y)) ∨ (τ (σ X0)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq28 eq224250
    | (have j0 := eq224250 X0
       grind)
    | exact resolve eq224250 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224250
  have eq224570 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ x = (M.op (k X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq28 eq224528
    | (have j0 := eq224528 X0
       grind)
    | exact resolve eq224528 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224528
  have eq224592 : ∀ X0 : G, x = (M.op (k X0 x) (M.op x y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq224570 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq224570
    | (have j0 := eq224570 X0
       grind)
    | exact resolve eq224570 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224570
  have eq225266 : (k (M.op x y) x) = (M.op (M.op (M.op x y) (k (M.op x y) x)) x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq224518 eq50
    | exact resolve eq50 eq224518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225419 : ∀ X0 : G, (k (M.op x X0) (M.op X0 X0)) = X0 ∨ (M.op x y) = (k (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq224518 eq18629
    | exact resolve eq18629 eq224518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224518
  have eq225532 : ∀ X0 : G, (k X0 x) = (M.op (M.op (M.op x y) (k X0 x)) x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq224592 eq50
    | (have j1 := eq224592 X0
       grind)
    | exact resolve eq50 eq224592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227991 : y = (k (M.op x y) (M.op y y)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq225419 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq225419
    | (have j0 := eq225419 y
       grind)
    | exact resolve eq225419 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225419
  have eq228196 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq227991 eq143
    | exact resolve eq143 eq227991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227991
  have eq228221 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq228196
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq228196
    | exact resolve eq228196 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228196
  have eq228254 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq228221 eq1999
    | (have j0 := eq1999 x (M.op x y)
       grind)
    | exact resolve eq1999 eq228221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228221
  have eq230130 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq228254 eq52
    | exact resolve eq52 eq228254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228254
  have eq237118 : (M.op x y) = (k (M.op (k (M.op x y) x) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq225266 eq18295
    | exact resolve eq18295 eq225266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225266
  have eq238189 : ∀ X0 : G, (M.op x y) = (k (M.op (k X0 x) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq225532 eq18295
    | (have j1 := eq225532 X0
       grind)
    | exact resolve eq18295 eq225532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18295 eq225532
  have eq245892 : ∀ X0 : G, (k (k (σ x) (σ y)) (σ X0)) = (σ (M.op (k x y) X0)) ∨ (k x y) = (k (k x y) X0) := by
    intro X0
    first
    | exact superpose eq60 eq2580
    | exact resolve eq2580 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq2580
  have eq246139 : ∀ X0 : G, (k (k (σ x) (σ y)) (σ X0)) = (σ (M.op x X0)) ∨ (k x y) = (k (k x y) X0) := by
    intro X0
    first
    | (have i₁ := eq245892 X0
       have i₂ := eq2715
       grind)
    | exact superpose eq2715 eq245892
    | (have j0 := eq245892 X0
       grind)
    | exact resolve eq245892 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245892
  have eq246189 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op x X0)) ∨ (k x y) = (k (k x y) X0) := by
    intro X0
    first
    | exact superpose eq2719 eq246139
    | (have j0 := eq246139 X0
       grind)
    | exact resolve eq246139 eq2719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2719 eq246139
  have eq246216 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ (k x y) = (k (k x y) X0) := by
    intro X0
    first
    | exact superpose eq35 eq246189
    | (have j0 := eq246189 X0
       grind)
    | exact resolve eq246189 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq246189
  have eq246231 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq246216 X0
       have i₂ := eq2715
       grind)
    | exact superpose eq2715 eq246216
    | (have j0 := eq246216 X0
       grind)
    | exact resolve eq246216 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246216
  have eq246266 : ∀ X0 : G, (σ (τ (k (σ x) X0))) = (σ (M.op x (τ X0))) ∨ x = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq246231 (τ X0)
       have i₂ := eq1222 X0
       grind)
    | exact superpose eq1222 eq246231
    | exact resolve eq246231 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222 eq246231
  have eq246554 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ x = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq246266 X0
       have i₂ := eq15 (k sF2 X0)
       grind)
    | exact superpose eq15 eq246266
    | (have j0 := eq246266 X0
       grind)
    | exact resolve eq246266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246266
  have eq247736 : ∀ X0 : G, (M.op x (τ X0)) = (τ (k (σ x) X0)) ∨ x = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op x (τ X0))
       have i₂ := eq246554 X0
       grind)
    | exact superpose eq246554 eq16
    | (have j1 := eq246554 X0
       grind)
    | exact resolve eq16 eq246554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246554
  have eq248437 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (τ (k (σ x) X0))) ∨ x = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 x (τ X0)
       have i₂ := eq247736 X0
       grind)
    | exact superpose eq247736 eq50
    | (have j1 := eq247736 X0
       grind)
    | exact resolve eq50 eq247736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247736
  have eq248900 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (τ (M.op (σ x) X0))) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq248437 (M.op (M.op sF2 x) (M.op sF2 x))
       have i₂ := eq36318 sF2 x
       grind)
    | exact superpose eq36318 eq248437
    | exact resolve eq248437 eq36318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36318
  have eq248955 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (k (τ (σ x)) X0)) ∨ x = (k (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq248437 (σ x)
       have i₂ := eq493 sF2 x
       grind)
    | exact superpose eq493 eq248437
    | exact resolve eq248437 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq248437
  have eq249217 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (k x X0)) ∨ x = (k (τ (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq28 eq248955
    | (have j0 := eq248955 X0
       grind)
    | exact resolve eq248955 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248955
  have eq249231 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (k x X0)) ∨ x = (k x X0) := by
    intro X0
    first
    | exact superpose eq28 eq249217
    | (have j0 := eq249217 X0
       grind)
    | exact resolve eq249217 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249217
  have eq249773 : ∀ X0 X1 : G, (k (M.op x X1) (M.op X1 X1)) = X1 ∨ x = (k x X0) := by
    intro X0 X1
    first
    | exact superpose eq249231 eq18629
    | (have j1 := eq249231 X0
       grind)
    | exact resolve eq18629 eq249231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249231
  have eq251161 : ∀ X0 : G, y = (k (M.op x y) (M.op y y)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq249773 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq249773
    | (have j0 := eq249773 X0 y
       grind)
    | exact resolve eq249773 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249773
  have eq251361 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ x = (k x X0) := by
    intro X0
    first
    | exact superpose eq251161 eq143
    | (have j1 := eq251161 X0
       grind)
    | exact resolve eq143 eq251161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251161
  have eq251386 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq251361 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq251361
    | (have j0 := eq251361 X0
       grind)
    | exact resolve eq251361 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251361
  have eq251419 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x X0) := by
    intro X0
    first
    | exact superpose eq251386 eq1999
    | (have j0 := eq1999 X0 x
       have j1 := eq251386 X0
       grind)
    | exact resolve eq1999 eq251386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251386
  have eq252481 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | exact superpose eq251419 eq52
    | (have j1 := eq251419 X1
       grind)
    | exact resolve eq52 eq251419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251419
  have eq256423 : x = (M.op (M.op (M.op x y) x) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq274 eq248900
    | (have j0 := eq248900 (σ y)
       grind)
    | exact resolve eq248900 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq248900
  have eq256946 : ∀ X0 : G, (k (M.op x X0) (M.op X0 X0)) = X0 ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq256423 eq18629
    | exact resolve eq18629 eq256423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18629 eq256423
  have eq258872 : y = (k (M.op x y) (M.op y y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq256946 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq256946
    | (have j0 := eq256946 y
       grind)
    | exact resolve eq256946 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256946
  have eq259076 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq258872 eq143
    | exact resolve eq143 eq258872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq258872
  have eq259101 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq259076
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq259076
    | exact resolve eq259076 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259076
  have eq259134 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq259101 eq1999
    | exact resolve eq1999 eq259101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259101
  have eq260704 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq259134 eq52
    | exact resolve eq52 eq259134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq259134
  have eq264518 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq224592 eq237118
    | (have j1 := eq224592 (M.op x y)
       grind)
    | exact resolve eq237118 eq224592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237118
  have eq264572 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq264518
  have eq264592 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq264572 eq160
    | exact resolve eq160 eq264572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264572
  have eq264641 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq20 eq264592
    | exact resolve eq264592 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264592
  have eq264717 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq264641 eq1999
    | (have j0 := eq1999 x (M.op x y)
       grind)
    | exact resolve eq1999 eq264641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264641
  have eq264770 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq264717 eq50
    | exact resolve eq50 eq264717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264717
  have eq265038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq264770 eq230130
    | exact resolve eq230130 eq264770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230130 eq264770
  have eq265231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq265038
  have eq265245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq265231
    | exact resolve eq265231 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265231
  have eq265255 : (M.op x y) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq265245
       have r₂ := eq27
       grind)
    | exact resolve eq265245 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265245
  have eq276660 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) ∨ (k X0 x) = X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq224592 eq238189
    | (have j0 := eq238189 X0
       have j1 := eq224592 X0
       grind)
    | exact resolve eq238189 eq224592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224592 eq238189
  have eq276726 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq276660 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276660
  have eq276752 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq160
       have i₂ := eq276726 (k x (M.op sF0 sF0))
       grind)
    | exact superpose eq276726 eq160
    | (have j1 := eq276726 X0
       grind)
    | exact resolve eq160 eq276726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq276726
  have eq276802 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq276752
    | (have j0 := eq276752 X0
       grind)
    | exact resolve eq276752 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276752
  have eq277341 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1999 X0 x
       have i₂ := eq276802 (k x X0)
       grind)
    | exact superpose eq276802 eq1999
    | (have j0 := eq1999 x X0
       have j1 := eq276802 X0
       grind)
    | exact resolve eq1999 eq276802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999 eq276802
  have eq277396 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op x y) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0 x
       have i₂ := eq277341 (M.op X0 x)
       grind)
    | exact superpose eq277341 eq50
    | (have j1 := eq277341 X0
       grind)
    | exact resolve eq50 eq277341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq277341
  have eq277670 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x X0) ∨ (σ (M.op x y)) = (σ x) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq252481 X0 X1
       have i₂ := eq277396 (M.op X0 sF1)
       grind)
    | exact superpose eq277396 eq252481
    | (have j0 := eq252481 X0 X0
       have j1 := eq277396 X1
       grind)
    | exact resolve eq252481 eq277396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252481 eq277396
  have eq277874 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x X0) ∨ (σ (M.op x y)) = (σ x) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | exact superpose eq26 eq277670
    | (have j0 := eq277670 X0 X1
       grind)
    | exact resolve eq277670 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277670
  have eq277881 : ∀ X0 X1 : G, x = (k x X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq277874 X0 X1
       grind)
    | (have r₁ := eq277874 X0 X1
       have r₂ := eq27
       grind)
    | exact resolve eq277874 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277874
  have eq325946 : x ≠ x ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by
    first
    | (have j0 := eq277881 x x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277881
  have eq325947 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by grind
  clear eq325946
  have eq325953 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq325947
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq325947
    | exact resolve eq325947 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq325947
  have eq326245 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq361 x
       have i₂ := eq325953
       grind)
    | exact superpose eq325953 eq361
    | exact resolve eq361 eq325953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326246 : x ≠ x ∨ (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq405 x
       have i₂ := eq325953
       grind)
    | exact superpose eq325953 eq405
    | (have r₁ := eq405 x
       have r₂ := eq325953
       grind)
    | exact resolve eq405 eq325953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq325953
  have eq326522 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq326246
  have eq332278 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq326522 eq265255
    | exact resolve eq265255 eq326522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265255 eq326522
  have eq332352 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq332278
  have eq332399 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq332352 eq266
    | exact resolve eq266 eq332352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq332352
  have eq333746 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq332399 eq326245
    | exact resolve eq326245 eq332399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326245 eq332399
  have eq333974 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq333746
  have eq333996 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq333974 eq29
    | exact resolve eq29 eq333974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333974
  have eq334509 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq333996
    | exact resolve eq333996 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333996
  have eq334531 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq334509 eq28
    | exact resolve eq28 eq334509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq334509
  have eq335287 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq334531
    | exact resolve eq334531 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq334531
  have eq335288 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq335287
  have eq335340 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq335288 eq142
    | exact resolve eq142 eq335288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq335386 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq335288 eq347
    | exact resolve eq347 eq335288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq335288
  have eq335894 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq335340
       have i₂ := eq122
       grind)
    | exact superpose eq122 eq335340
    | exact resolve eq335340 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335340
  have eq337702 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq335386 (M.op y x)
       have i₂ := eq335386 x
       grind)
    | exact superpose eq335386 eq335386
    | exact resolve eq335386 eq335386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335386
  have eq337948 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq337702
  have eq338221 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq337948
       grind)
    | exact superpose eq337948 eq122
    | exact resolve eq122 eq337948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq337948
  have eq338595 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq338221
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq338221
    | exact resolve eq338221 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq338221
  have eq345436 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq335894 eq338595
    | exact resolve eq338595 eq335894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335894 eq338595
  have eq345759 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq345436
  have eq345878 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq345759 eq163
    | exact resolve eq163 eq345759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq345759
  have eq346280 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq345878
    | exact resolve eq345878 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq345878
  have eq347411 : y = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq346280 eq18202
    | exact resolve eq18202 eq346280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18202 eq346280
  have eq347824 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq347411
       have i₂ := eq2715
       grind)
    | exact superpose eq2715 eq347411
    | exact resolve eq347411 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347411
  have eq347825 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq347824
  have eq350220 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq347825
       grind)
    | exact superpose eq347825 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq347825
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq347825
       grind)
    | exact resolve eq13 eq347825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347825
  have eq350398 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq350220
  have eq350505 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq350398
       have i₂ := eq2715
       grind)
    | exact superpose eq2715 eq350398
    | exact resolve eq350398 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2715 eq350398
  have eq350510 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq350505
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq350505
    | exact resolve eq350505 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq350505
  have eq350511 : x = (M.op x y) := by grind
  clear eq350510
  have eq350513 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq350511 eq20
    | exact resolve eq20 eq350511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq350561 : x = (M.op (M.op x x) x) := by
    first
    | exact superpose eq350511 eq252
    | exact resolve eq252 eq350511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq351030 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq350513
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq350513
    | exact resolve eq350513 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350513
  have eq351653 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq351030 eq26
    | exact resolve eq26 eq351030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq352687 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq361 (M.op x x)
       have i₂ := eq350561
       grind)
    | exact superpose eq350561 eq361
    | exact resolve eq361 eq350561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq350561
  have eq352981 : x = (M.op x x) := by
    first
    | exact superpose eq350511 eq352687
    | exact resolve eq352687 eq350511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350511 eq352687
  have eq353051 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq352981
       grind)
    | exact superpose eq352981 eq123
    | exact resolve eq123 eq352981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq352981
  have eq353619 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq351030 eq353051
    | exact resolve eq353051 eq351030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353051
  have eq353728 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq353619
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq353619
    | exact resolve eq353619 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353619
  have eq353782 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq351030 eq353728
    | exact resolve eq353728 eq351030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353728
  have eq353867 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq353782 eq260704
    | exact resolve eq260704 eq353782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260704
  have eq354223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq351653 eq353867
    | exact resolve eq353867 eq351653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353867
  have eq354315 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq354223
       have r₂ := eq27
       grind)
    | exact resolve eq354223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354223
  have eq365229 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq354315 eq15
    | exact resolve eq15 eq354315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354315
  have eq365497 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq365229
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq365229
    | exact resolve eq365229 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq365229
  have eq365550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq351030 eq365497
    | exact resolve eq365497 eq351030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351030 eq365497
  have eq365579 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq365550
       have r₂ := eq27
       grind)
    | exact resolve eq365550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365550
  have eq365914 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq365579 eq351653
    | exact resolve eq351653 eq365579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351653 eq365579
  have eq365919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq353782 eq365914
    | exact resolve eq365914 eq353782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353782 eq365914
  have eq366012 : False := by grind
  exact eq366012

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq61 X3 X0 x
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq350 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq351 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq352 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq347 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq347 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq347 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq373 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq352 (σ X0)
       grind)
    | exact superpose eq352 eq15
    | exact resolve eq15 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq373 X0
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq373
    | exact resolve eq373 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq373
  have eq484 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq351 (τ X1) X0
       grind)
    | exact superpose eq351 eq18
    | (have j1 := eq351 (τ X1) X0
       grind)
    | exact resolve eq18 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq487 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq351 (σ X1) (σ X0)
       grind)
    | exact superpose eq351 eq15
    | (have j1 := eq351 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq1076 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq484
    | exact resolve eq484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq1137 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1076
    | (have j0 := eq1076 X0 X1
       grind)
    | exact resolve eq1076 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1885 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq487 x y
       grind)
    | exact superpose eq487 eq16
    | (have j1 := eq487 x y
       grind)
    | exact resolve eq16 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1930 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq487 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq2074 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1885
       have i₂ := eq1137 y x
       grind)
    | exact superpose eq1137 eq1885
    | (have j1 := eq1137 (σ y) (σ x)
       grind)
    | (have r₁ := eq1885
       have r₂ := eq1137 y x
       grind)
    | exact resolve eq1885 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq2075 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2074
  have eq2082 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2075
       grind)
    | exact superpose eq2075 eq61
    | exact resolve eq61 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2083 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y x
       have i₂ := eq2075
       grind)
    | exact superpose eq2075 eq62
    | exact resolve eq62 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2144 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2083 y
       have i₂ := eq2075
       grind)
    | exact superpose eq2075 eq2083
    | exact resolve eq2083 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075 eq2083
  have eq2161 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq2144
  have eq2172 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq2161
       grind)
    | exact superpose eq2161 eq61
    | exact resolve eq61 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq2322 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2172 (M.op x (σ x))
       have i₂ := eq2172 x
       grind)
    | exact superpose eq2172 eq2172
    | exact resolve eq2172 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172
  have eq2349 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2322
  have eq2352 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2349
       have i₂ := eq392 x
       grind)
    | exact superpose eq392 eq2349
    | exact resolve eq2349 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349
  have eq2384 : ∀ X0 X1 : G, (σ x) = (σ (M.op x x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq69 x X1 x x
       have i₂ := eq2352
       grind)
    | exact superpose eq2352 eq69
    | exact resolve eq69 eq2352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2352
  have eq2737 : ∀ X0 X1 : G, (M.op x x) = (τ (σ x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2384 X0 X1
       grind)
    | exact superpose eq2384 eq10
    | (have j1 := eq2384 X0 X1
       grind)
    | exact resolve eq10 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384
  have eq2796 : ∀ X0 X1 : G, x = (M.op x x) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2737 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2737
    | (have j0 := eq2737 X0 X1
       grind)
    | exact resolve eq2737 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq2828 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op (M.op (M.op X1 X2) x) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 x X1 x
       have i₂ := eq2796 X0 X1
       grind)
    | exact superpose eq2796 eq67
    | (have j1 := eq2796 X1 X2
       grind)
    | exact resolve eq67 eq2796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2796
  have eq2890 : ∀ X0 X1 : G, x ≠ x ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq2828 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828
  have eq2891 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq2890 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq2947 : x = (M.op x x) := by
    first
    | (have i₁ := eq2891 (M.op x x) x
       have i₂ := eq2891 x x
       grind)
    | exact superpose eq2891 eq2891
    | exact resolve eq2891 eq2891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2964 : ∀ X2 : G, x = (M.op x (M.op x X2)) := by
    intro X2
    first
    | (have i₁ := eq61 (M.op (M.op x x) x) x X2
       have i₂ := eq2891 x x
       grind)
    | exact superpose eq2891 eq61
    | exact resolve eq61 eq2891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2968 : ∀ X2 : G, x = (M.op (M.op X2 x) x) := by
    intro X2
    first
    | (have i₁ := eq67 x x (M.op (M.op x x) x)
       have i₂ := eq2891 x x
       grind)
    | exact superpose eq2891 eq67
    | exact resolve eq67 eq2891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2891
  have eq3028 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (M.op (M.op x X0) x) ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x (M.op x X0)
       have i₂ := eq2964 X0
       grind)
    | exact superpose eq2964 eq13
    | (have j0 := eq13 x (M.op x X0)
       grind)
    | (have r₁ := eq13 x (M.op x x)
       have r₂ := eq2964 x
       grind)
    | exact resolve eq13 eq2964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2964
  have eq3040 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) x) ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq3028 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028
  have eq3042 : ∀ X0 : G, x = (k x (M.op x X0)) ∨ (M.op x X0) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3040 X0
       have i₂ := eq2947
       grind)
    | exact superpose eq2947 eq3040
    | (have j0 := eq3040 X0
       grind)
    | exact resolve eq3040 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq3811 : x = (k x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3042 (M.op y x)
       have i₂ := eq2082 x
       grind)
    | exact superpose eq2082 eq3042
    | exact resolve eq3042 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082 eq3042
  have eq12636 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1930 x y
       have i₂ := eq3811
       grind)
    | exact superpose eq3811 eq1930
    | (have j0 := eq1930 x y
       grind)
    | exact resolve eq1930 eq3811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930 eq3811
  have eq12653 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq12636
  have eq12654 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12653
  have eq12675 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2968 y
       have i₂ := eq12654
       grind)
    | exact superpose eq12654 eq2968
    | exact resolve eq2968 eq12654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968
  have eq12715 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12654
       have i₂ := eq12675
       grind)
    | exact superpose eq12675 eq12654
    | exact resolve eq12654 eq12675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12654 eq12675
  have eq12750 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12715
  have eq12754 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12750
       grind)
    | exact superpose eq12750 eq16
    | exact resolve eq16 eq12750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12750
  have eq12791 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12754
       have r₂ := eq392 x
       grind)
    | exact resolve eq12754 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12754
  have eq12797 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12791
       grind)
    | exact superpose eq12791 eq16
    | exact resolve eq16 eq12791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12813 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq12791
       grind)
    | exact superpose eq12791 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12791
       grind)
    | exact resolve eq12 eq12791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12814 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq12791
       grind)
    | exact superpose eq12791 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq12791
       grind)
    | exact resolve eq13 eq12791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12816 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq12791
       grind)
    | exact superpose eq12791 eq61
    | exact resolve eq61 eq12791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq12836 : (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq12814
  have eq12837 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
  clear eq12813
  have eq12843 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12836
       have i₂ := eq392 x
       grind)
    | exact superpose eq392 eq12836
    | exact resolve eq12836 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq12836
  have eq12844 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq12837
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12837
    | exact resolve eq12837 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12837
  have eq12856 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12843
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq12843
    | exact resolve eq12843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12843
  have eq12861 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12856
       have i₂ := eq2947
       grind)
    | exact superpose eq2947 eq12856
    | exact resolve eq12856 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12856
  have eq12865 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12861
       have i₂ := eq12844
       grind)
    | exact superpose eq12844 eq12861
    | exact resolve eq12861 eq12844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12861
  have eq13118 : (σ y) = (M.op (σ x) (σ (k y x))) := by
    first
    | (have i₁ := eq12816 (σ x)
       have i₂ := eq12844
       grind)
    | exact superpose eq12844 eq12816
    | exact resolve eq12816 eq12844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12816 eq12844
  have eq14312 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1137 y x
       have i₂ := eq12865
       grind)
    | exact superpose eq12865 eq1137
    | (have j0 := eq1137 y x
       grind)
    | exact resolve eq1137 eq12865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq12865
  have eq14379 : x = (M.op x y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq14312
       have r₂ := eq12797
       grind)
    | exact resolve eq14312 eq12797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14312
  have eq14446 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12797
       have i₂ := eq14379
       grind)
    | exact superpose eq14379 eq12797
    | exact resolve eq12797 eq14379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14379
  have eq14483 : (σ y) = (σ (k y x)) := by grind
  clear eq14446
  have eq14504 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13118
       have i₂ := eq14483
       grind)
    | exact superpose eq14483 eq13118
    | exact resolve eq13118 eq14483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13118 eq14483
  have eq14582 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14504
       have i₂ := eq12791
       grind)
    | exact superpose eq12791 eq14504
    | exact resolve eq14504 eq12791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12791 eq14504
  have eq14675 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14582
       grind)
    | exact superpose eq14582 eq10
    | exact resolve eq10 eq14582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14582
  have eq14748 : x = y := by
    first
    | (have i₁ := eq14675
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14675
    | exact resolve eq14675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14675
  have eq14795 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12797
       have i₂ := eq14748
       grind)
    | exact superpose eq14748 eq12797
    | exact resolve eq12797 eq14748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12797 eq14748
  have eq14826 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq14795
       have i₂ := eq2947
       grind)
    | exact superpose eq2947 eq14795
    | exact resolve eq14795 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947 eq14795
  have eq14827 : False := by grind
  exact eq14827

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq61 X3 X0 x
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq350 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq351 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq352 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq347 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq347 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq347 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq373 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq352 (σ X0)
       grind)
    | exact superpose eq352 eq15
    | exact resolve eq15 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq373 X0
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq373
    | exact resolve eq373 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq373
  have eq484 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq351 (τ X1) X0
       grind)
    | exact superpose eq351 eq18
    | (have j1 := eq351 (τ X1) X0
       grind)
    | exact resolve eq18 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq487 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq351 (σ X1) (σ X0)
       grind)
    | exact superpose eq351 eq15
    | (have j1 := eq351 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq1064 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq484
    | exact resolve eq484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq1125 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1064 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1064
    | (have j0 := eq1064 X0 X1
       grind)
    | exact resolve eq1064 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1898 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq487 x y
       grind)
    | exact superpose eq487 eq16
    | (have j1 := eq487 x y
       grind)
    | exact resolve eq16 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1943 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq487 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq2096 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1898
       have i₂ := eq1125 y x
       grind)
    | exact superpose eq1125 eq1898
    | (have j1 := eq1125 (σ y) (σ x)
       grind)
    | (have r₁ := eq1898
       have r₂ := eq1125 y x
       grind)
    | exact resolve eq1898 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq2097 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2096
  have eq2103 : x ≠ x ∨ y = (M.op y x) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2097
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2097
       grind)
    | exact resolve eq13 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2105 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq61
    | exact resolve eq61 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2106 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y x
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq62
    | exact resolve eq62 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2114 : x = (k x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2103
  have eq2166 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2106 y
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq2106
    | exact resolve eq2106 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106
  have eq2183 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq2166
  have eq2240 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq2183
       grind)
    | exact superpose eq2183 eq61
    | exact resolve eq61 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183
  have eq2352 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2240 (M.op x (σ x))
       have i₂ := eq2240 x
       grind)
    | exact superpose eq2240 eq2240
    | exact resolve eq2240 eq2240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2240
  have eq2380 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2352
  have eq2383 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2380
       have i₂ := eq392 x
       grind)
    | exact superpose eq392 eq2380
    | exact resolve eq2380 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq2415 : ∀ X0 X1 : G, (σ x) = (σ (M.op x x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq69 x X1 x x
       have i₂ := eq2383
       grind)
    | exact superpose eq2383 eq69
    | exact resolve eq69 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2383
  have eq2772 : ∀ X0 X1 : G, (τ (σ x)) = (M.op x x) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2415 X0 X1
       grind)
    | exact superpose eq2415 eq10
    | (have j1 := eq2415 X0 X1
       grind)
    | exact resolve eq10 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq2831 : ∀ X0 X1 : G, x = (M.op x x) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2772 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2772
    | (have j0 := eq2772 X0 X1
       grind)
    | exact resolve eq2772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2772
  have eq2863 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op (M.op (M.op X1 X2) x) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 x X1 x
       have i₂ := eq2831 X0 X1
       grind)
    | exact superpose eq2831 eq67
    | (have j1 := eq2831 X1 X2
       grind)
    | exact resolve eq67 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2831
  have eq2928 : ∀ X0 X1 : G, x ≠ x ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq2863 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq2929 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq2928 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928
  have eq2985 : x = (M.op x x) := by
    first
    | (have i₁ := eq2929 (M.op x x) x
       have i₂ := eq2929 x x
       grind)
    | exact superpose eq2929 eq2929
    | exact resolve eq2929 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq8503 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1943 x y
       have i₂ := eq2114
       grind)
    | exact superpose eq2114 eq1943
    | (have j0 := eq1943 x y
       grind)
    | exact resolve eq1943 eq2114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943 eq2114
  have eq8516 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq8503
  have eq8517 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8516
  have eq8532 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2105 x
       have i₂ := eq8517
       grind)
    | exact superpose eq8517 eq2105
    | exact resolve eq2105 eq8517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105 eq8517
  have eq8566 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8532
  have eq8641 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2097
       have i₂ := eq8566
       grind)
    | exact superpose eq8566 eq2097
    | exact resolve eq2097 eq8566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097 eq8566
  have eq8670 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8641
  have eq8672 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8670
       grind)
    | exact superpose eq8670 eq16
    | exact resolve eq16 eq8670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8670
  have eq8707 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8672
       have r₂ := eq392 x
       grind)
    | exact resolve eq8672 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq8672
  have eq8711 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8707
       grind)
    | exact superpose eq8707 eq16
    | exact resolve eq16 eq8707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8727 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq8707
       grind)
    | exact superpose eq8707 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8707
       grind)
    | exact resolve eq12 eq8707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8728 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq8707
       grind)
    | exact superpose eq8707 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8707
       grind)
    | exact resolve eq13 eq8707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8730 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq8707
       grind)
    | exact superpose eq8707 eq61
    | exact resolve eq61 eq8707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq8747 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq8728
  have eq8748 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
  clear eq8727
  have eq8752 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8747
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8747
    | exact resolve eq8747 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8747
  have eq8753 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq8748
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8748
    | exact resolve eq8748 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8748
  have eq8979 : (σ y) = (M.op (σ x) (σ (k y x))) := by
    first
    | (have i₁ := eq8730 (σ x)
       have i₂ := eq8753
       grind)
    | exact superpose eq8753 eq8730
    | exact resolve eq8730 eq8753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8730
  have eq10841 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1125 y x
       have i₂ := eq8752
       grind)
    | exact superpose eq8752 eq1125
    | (have j0 := eq1125 y x
       grind)
    | exact resolve eq1125 eq8752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq8752
  have eq10926 : x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq10841
       have r₂ := eq8711
       grind)
    | exact resolve eq10841 eq8711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10841
  have eq10952 : x = (M.op x y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10926
       have i₂ := eq8753
       grind)
    | exact superpose eq8753 eq10926
    | exact resolve eq10926 eq8753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8753 eq10926
  have eq11015 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq8711
       have i₂ := eq10952
       grind)
    | exact superpose eq10952 eq8711
    | exact resolve eq8711 eq10952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10952
  have eq11051 : (σ y) = (σ (k y x)) := by grind
  clear eq11015
  have eq11071 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8979
       have i₂ := eq11051
       grind)
    | exact superpose eq11051 eq8979
    | exact resolve eq8979 eq11051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8979 eq11051
  have eq11148 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11071
       have i₂ := eq8707
       grind)
    | exact superpose eq8707 eq11071
    | exact resolve eq11071 eq8707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8707 eq11071
  have eq11246 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11148
       grind)
    | exact superpose eq11148 eq10
    | exact resolve eq10 eq11148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11148
  have eq11320 : x = y := by
    first
    | (have i₁ := eq11246
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11246
    | exact resolve eq11246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11246
  have eq11382 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8711
       have i₂ := eq11320
       grind)
    | exact superpose eq11320 eq8711
    | exact resolve eq8711 eq11320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8711 eq11320
  have eq11423 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11382
       have i₂ := eq2985
       grind)
    | exact superpose eq2985 eq11382
    | exact resolve eq11382 eq2985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985 eq11382
  have eq11424 : False := by grind
  exact eq11424

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pxx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq85 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq78 eq53
    | exact resolve eq53 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ (M.op x y) = (k y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq83 eq12
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ x = (k (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq80 eq12
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq81 eq12
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op x x)
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq109 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq109 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq119 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq15
    | exact resolve eq15 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq119
    | exact resolve eq119 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq126 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq85 eq12
    | exact resolve eq12 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq193 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq10
    | exact resolve eq10 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq28
    | exact resolve eq28 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq199 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 (M.op X0 X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq31
    | exact resolve eq31 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq201 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq36
    | exact resolve eq36 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq150
    | exact resolve eq150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq237 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq193 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq193
    | exact resolve eq193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq321 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq340 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 X1
       have i₂ := eq120 (τ X0)
       grind)
    | exact superpose eq120 eq321
    | (have j0 := eq321 X0 X1
       grind)
    | exact resolve eq321 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq343 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq340 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq340
    | (have j0 := eq340 X0 X1
       grind)
    | exact resolve eq340 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq358 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 x) x) X0
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 (M.op (M.op x x) x) x
       have r₂ := eq54 x x x
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 x) x) X0
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1249 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq196 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq196
    | (have j0 := eq196 x
       grind)
    | exact resolve eq196 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1250 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq196 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq196
    | (have j0 := eq196 y
       grind)
    | exact resolve eq196 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1794 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq199
    | (have j0 := eq199 (M.op x y)
       grind)
    | exact resolve eq199 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq1970 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq201
    | (have j0 := eq201 (M.op x y)
       grind)
    | exact resolve eq201 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq8350 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq108
    | (have j0 := eq108 (M.op x y) y
       grind)
    | (have r₁ := eq108 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq108 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq8351 : x ≠ x ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq108
    | (have j0 := eq108 x (M.op x y)
       grind)
    | (have r₁ := eq108 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq108 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq8352 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq85 eq108
    | (have j0 := eq108 (M.op (σ x) (σ y)) (σ y)
       grind)
    | (have r₁ := eq108 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq85 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq108 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq8353 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq81 eq108
    | (have j0 := eq108 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq108 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq81 (σ x)
       grind)
    | exact resolve eq108 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq108
  have eq8358 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by grind
  clear eq8353
  have eq8359 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by grind
  clear eq8352
  have eq8360 : x = (M.op x x) ∨ x = (k (M.op x y) (M.op x x)) := by grind
  clear eq8351
  have eq8361 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq8350
  have eq8366 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | (have j1 := eq97 (σ x)
       grind)
    | (have r₁ := eq8358
       have r₂ := eq97 (σ x)
       grind)
    | exact resolve eq8358 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq8358
  have eq8367 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have j1 := eq126 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq8359
       have r₂ := eq126 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq8359 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq8359
  have eq8368 : x = (k (M.op x y) (M.op x x)) := by
    first
    | (have j1 := eq96 x
       grind)
    | (have r₁ := eq8360
       have r₂ := eq96 x
       grind)
    | exact resolve eq8360 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq8360
  have eq8369 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have j1 := eq95 (M.op x y)
       grind)
    | (have r₁ := eq8361
       have r₂ := eq95 (M.op x y)
       grind)
    | exact resolve eq8361 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq8361
  have eq8375 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq8368 eq1249
    | exact resolve eq1249 eq8368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249 eq8368
  have eq8378 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq8369 eq1970
    | exact resolve eq1970 eq8369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970 eq8369
  have eq8380 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq8375
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8375
    | exact resolve eq8375 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8375
  have eq8383 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq8378
    | exact resolve eq8378 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8378
  have eq8389 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) ≠ (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq358 X1 X1 X2
       have i₂ := eq343 X0 X1
       grind)
    | (have i₁ := eq358 X1 (τ X0) X2
       have i₂ := eq343 X0 X1
       grind)
    | exact superpose eq343 eq358
    | (have j0 := eq358 X0 (τ X1) X2
       have j1 := eq343 X1 X0
       grind)
    | (have r₁ := eq358 X1 (τ X0) X2
       have r₂ := eq343 X0 X1
       grind)
    | (have r₁ := eq358 (τ X0) (τ X0) X2
       have r₂ := eq343 X0 (τ X0)
       grind)
    | exact resolve eq358 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq358
  have eq8400 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) ≠ (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq8389 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8389
  have eq8401 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq8400 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8400
  have eq8404 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq8401 X0 X1 X2
       have j1 := eq359 X0 (τ X1) X2
       grind)
    | (have r₁ := eq8401 X0 X1 X2
       have r₂ := eq359 X0 (τ X1) X2
       grind)
    | exact resolve eq8401 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq8401
  have eq8409 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq8366 eq205
    | exact resolve eq205 eq8366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8410 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) (M.op (τ (σ x)) (τ (σ x)))) := by
    first
    | (have i₁ := eq8409
       have i₂ := eq237 sF2
       grind)
    | exact superpose eq237 eq8409
    | exact resolve eq8409 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8409
  have eq8415 : x = (k (τ (M.op (σ x) (σ y))) (M.op x x)) := by
    first
    | exact superpose eq38 eq8410
    | exact resolve eq8410 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8410
  have eq8444 : (τ (M.op (σ x) (σ y))) = (k (τ (σ y)) (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq8367 eq205
    | exact resolve eq205 eq8367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq8445 : (τ (M.op (σ x) (σ y))) = (k (τ (σ y)) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq8444
       have i₂ := eq237 sF4
       grind)
    | exact superpose eq237 eq8444
    | exact resolve eq8444 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8444
  have eq8451 : (τ (M.op (σ x) (σ y))) = (k y (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq39 eq8445
    | exact resolve eq8445 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8445
  have eq211124 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8404 X1 X0 (M.op (τ X0) x)
       have i₂ := eq53 X1 (τ X0) x
       grind)
    | exact superpose eq53 eq8404
    | (have j0 := eq8404 X1 X0 x
       grind)
    | exact resolve eq8404 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8404
  have eq211133 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (k (σ y) (σ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq39 eq211124
    | (have j0 := eq211124 (σ y) X0
       grind)
    | exact resolve eq211124 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211143 : x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq8415
       have i₂ := eq211124 sF4 (M.op x x)
       grind)
    | exact superpose eq211124 eq8415
    | (have j1 := eq211124 (M.op (σ x) (σ y)) (M.op x x)
       grind)
    | exact resolve eq8415 eq211124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8415 eq211124
  have eq211160 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq211143
       have i₂ := eq120 x
       grind)
    | exact superpose eq120 eq211143
    | exact resolve eq211143 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211143
  have eq211166 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ y)) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq36 eq211133
    | (have j0 := eq211133 X0
       grind)
    | exact resolve eq211133 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq211133
  have eq211175 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq211160
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq211160
    | exact resolve eq211160 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq211160
  have eq211177 : x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq8366 eq211175
    | exact resolve eq211175 eq8366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8366 eq211175
  have eq211185 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) X0)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq211177 eq53
    | exact resolve eq53 eq211177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211187 : ∀ X0 : G, x = (M.op (M.op X0 x) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq211177 eq82
    | exact resolve eq82 eq211177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211177
  have eq211228 : (M.op (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) y) := by
    first
    | exact superpose eq8451 eq211166
    | exact resolve eq211166 eq8451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8451
  have eq211401 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq211228
       have i₂ := eq11 sF4
       grind)
    | exact superpose eq11 eq211228
    | exact resolve eq211228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211228
  have eq212035 : ∀ X0 : G, y = (M.op (τ (M.op (σ x) (σ y))) (M.op y X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq211401 eq53
    | exact resolve eq53 eq211401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq211401
  have eq212044 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq212035 eq211185
    | exact resolve eq211185 eq212035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211185 eq212035
  have eq212059 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq212044
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq212044
    | exact resolve eq212044 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212044
  have eq212090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq212059 eq11
    | exact resolve eq11 eq212059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212059
  have eq212124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq212090
    | exact resolve eq212090 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212090
  have eq212125 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq212124
       have r₂ := eq27
       grind)
    | exact resolve eq212124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212124
  have eq212127 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq212125 eq8367
    | exact resolve eq8367 eq212125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8367 eq212125
  have eq212282 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq59 eq212127
    | exact resolve eq212127 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq212127
  have eq212688 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq211166 x
       have i₂ := eq212282
       grind)
    | exact superpose eq212282 eq211166
    | (have j0 := eq211166 x
       grind)
    | exact resolve eq211166 eq212282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211166
  have eq212926 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq212688
  have eq212981 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq212926
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq212926
    | exact resolve eq212926 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212926
  have eq213152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq212282
       have i₂ := eq212981
       grind)
    | exact superpose eq212981 eq212282
    | exact resolve eq212282 eq212981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212282 eq212981
  have eq213200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq213152
  have eq213220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq213200
    | exact resolve eq213200 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213200
  have eq213244 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq213220
       have r₂ := eq27
       grind)
    | exact resolve eq213220 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213220
  have eq213274 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq213244 eq1250
    | exact resolve eq1250 eq213244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq214244 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq213244 eq78
    | exact resolve eq78 eq213244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq214250 : (M.op (τ (σ y)) (τ (σ y))) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq213244 eq237
    | exact resolve eq237 eq213244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq214399 : (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq39 eq214250
    | exact resolve eq214250 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214250
  have eq214433 : ∀ X0 : G, (σ x) = (σ y) ∨ x = (M.op (M.op X0 x) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq214244 eq211187
    | (have j0 := eq211187 X0
       grind)
    | exact resolve eq211187 eq214244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211187 eq214244
  have eq214549 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq214399 eq214433
    | exact resolve eq214433 eq214399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214399 eq214433
  have eq234434 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq82 y (M.op x x) y
       have i₂ := eq214549 x
       grind)
    | exact superpose eq214549 eq82
    | exact resolve eq82 eq214549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq214549
  have eq234452 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq234434
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq234434
    | exact resolve eq234434 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234434
  have eq234473 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120 y
       have i₂ := eq234452
       grind)
    | exact superpose eq234452 eq120
    | exact resolve eq120 eq234452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234452
  have eq234608 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq234473
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq234473
    | exact resolve eq234473 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq234473
  have eq234644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq213244 eq234608
    | exact resolve eq234608 eq213244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234608
  have eq234674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq234644
    | exact resolve eq234644 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234644
  have eq234703 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq234674
       have r₂ := eq27
       grind)
    | exact resolve eq234674 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234674
  have eq234712 : y = (τ (σ x)) := by
    first
    | exact superpose eq234703 eq39
    | exact resolve eq39 eq234703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq235204 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq234703 eq8383
    | exact resolve eq8383 eq234703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8383
  have eq241170 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq234703 eq213244
    | exact resolve eq213244 eq234703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213244 eq234703
  have eq245080 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq241170 eq8380
    | exact resolve eq8380 eq241170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8380
  have eq245709 : (σ (M.op x y)) = (σ (k x (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq1794 eq235204
    | exact resolve eq235204 eq1794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235204
  have eq245733 : x = y := by
    first
    | exact superpose eq38 eq234712
    | exact resolve eq234712 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq234712
  have eq245794 : (σ x) = (σ (k (M.op x y) (M.op y y))) := by
    first
    | exact superpose eq213274 eq245080
    | exact resolve eq245080 eq213274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213274 eq245080
  have eq245950 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq245709 eq1794
    | exact resolve eq1794 eq245709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794 eq245709
  have eq246683 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq245733
       grind)
    | exact superpose eq245733 eq18
    | exact resolve eq18 eq245733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq258138 : (σ x) = (σ (k (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq245794
       have i₂ := eq245733
       grind)
    | exact superpose eq245733 eq245794
    | exact resolve eq245794 eq245733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245733 eq245794
  have eq259972 : (σ x) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq258138
       have i₂ := eq246683
       grind)
    | exact superpose eq246683 eq258138
    | exact resolve eq258138 eq246683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246683 eq258138
  have eq260565 : (σ x) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq259972
       have i₂ := eq110 sF0
       grind)
    | exact superpose eq110 eq259972
    | exact resolve eq259972 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259972
  have eq261066 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq260565
       have i₂ := eq120 sF0
       grind)
    | exact superpose eq120 eq260565
    | exact resolve eq260565 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq260565
  have eq261132 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq261066
    | exact resolve eq261066 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq261066
  have eq261447 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq261132 eq245950
    | exact resolve eq245950 eq261132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245950 eq261132
  have eq261592 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq261447
       have i₂ := eq110 sF2
       grind)
    | exact superpose eq110 eq261447
    | exact resolve eq261447 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq261447
  have eq261622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq241170 eq261592
    | exact resolve eq261592 eq241170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241170 eq261592
  have eq261629 : False := by grind
  exact eq261629

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyy_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq214 eq14
    | exact resolve eq14 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq273 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq262 eq50
    | exact resolve eq50 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq612 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq78 X0 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq624 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq612 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq612 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq612 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq612 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq628 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq624
    | (have j0 := eq624 X0 X1
       grind)
    | exact resolve eq624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq1063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1063
    | exact resolve eq1063 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1067 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1064
       have r₂ := eq27
       grind)
    | exact resolve eq1064 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1069 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1067
    | exact resolve eq1067 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1071 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1069
    | exact resolve eq1069 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1073 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1071 eq27
    | exact resolve eq27 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1071 eq116
    | (have r₁ := eq116
       have r₂ := eq1071
       grind)
    | exact resolve eq116 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1084 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1071 eq263
    | exact resolve eq263 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1071
  have eq1091 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1076
  have eq1143 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1084 eq1084
    | exact resolve eq1084 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1163 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1143
  have eq2552 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1091
       have r₂ := eq1090
       grind)
    | exact resolve eq1091 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq1091
  have eq2555 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2552 eq101
    | exact resolve eq101 eq2552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq2558 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2555
  have eq2569 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2558 eq1163
    | exact resolve eq1163 eq2558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163 eq2558
  have eq2593 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2569
  have eq2599 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2593
       have r₂ := eq1073
       grind)
    | exact resolve eq2593 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073 eq2593
  have eq2604 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2599 eq27
    | exact resolve eq27 eq2599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2606 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2599 eq67
    | (have r₁ := eq67
       have r₂ := eq2599
       grind)
    | exact resolve eq67 eq2599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq2607 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2599 eq215
    | exact resolve eq215 eq2599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq2620 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2606
  have eq2626 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2607 eq273
    | exact resolve eq273 eq2607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607
  have eq2644 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2599 eq2626
    | exact resolve eq2626 eq2599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2599 eq2626
  have eq2663 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2644
  have eq2998 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2620 eq101
    | exact resolve eq101 eq2620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq2620
  have eq3001 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2998
  have eq3014 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3001 eq2663
    | exact resolve eq2663 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663 eq3001
  have eq3039 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3014
  have eq3043 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3039
       have r₂ := eq2604
       grind)
    | exact resolve eq3039 eq2604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2604 eq3039
  have eq3045 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3043 eq20
    | exact resolve eq20 eq3043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3049 : (σ (k y y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3043 eq77
    | exact resolve eq77 eq3043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq3061 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3043 eq262
    | exact resolve eq262 eq3043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3073 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq3084 : (k (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3049
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq3049
    | exact resolve eq3049 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049
  have eq3087 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3045
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3045
    | exact resolve eq3045 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq3343 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3061 (M.op y x)
       have i₂ := eq3061 x
       grind)
    | exact superpose eq3061 eq3061
    | exact resolve eq3061 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3349 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq262 (M.op y x)
       have i₂ := eq3061 x
       grind)
    | exact superpose eq3061 eq262
    | exact resolve eq262 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq3061
  have eq3372 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq3343
  have eq3384 : y ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3349 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3349
       grind)
    | exact resolve eq13 eq3349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq3406 : (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3384
       have r₂ := eq3043
       grind)
    | exact resolve eq3384 eq3043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384
  have eq3416 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq3372
       grind)
    | exact superpose eq3372 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq3372
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3372
       grind)
    | exact resolve eq13 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3434 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq3416
  have eq3446 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq3434
       grind)
    | exact superpose eq3434 eq76
    | exact resolve eq76 eq3434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq3434
  have eq3452 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3446
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3446
    | exact resolve eq3446 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq3460 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3452 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq3452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3461 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3460
  have eq3480 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3461 eq263
    | exact resolve eq263 eq3461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq3461
  have eq4096 : (k y y) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3084 eq107
    | exact resolve eq107 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq4101 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3084 eq3452
    | exact resolve eq3452 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084 eq3452
  have eq4104 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq4101
  have eq4115 : (k y y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114 eq4096
    | exact resolve eq4096 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4096
  have eq4120 : (τ (σ y)) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4104 eq114
    | exact resolve eq114 eq4104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq4104
  have eq4127 : y = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4120
    | exact resolve eq4120 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4120
  have eq5254 : (k y y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq3043 eq3406
    | exact resolve eq3406 eq3043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3043
  have eq5266 : (k y y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3406 eq4115
    | exact resolve eq4115 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115
  have eq5267 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3406 eq4127
    | exact resolve eq4127 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406 eq4127
  have eq5272 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5267
  have eq5273 : (k y y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5266
  have eq5284 : (k y y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5254
       have r₂ := eq3073
       grind)
    | exact resolve eq5254 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073 eq5254
  have eq5292 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5272 eq294
    | exact resolve eq294 eq5272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq5272
  have eq7370 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5273
       have i₂ := eq5284
       grind)
    | exact superpose eq5284 eq5273
    | exact resolve eq5273 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273 eq5284
  have eq7380 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq7370
  have eq7407 : (M.op x y) = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7380 eq223
    | exact resolve eq223 eq7380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq7380
  have eq8710 : (M.op x y) ≠ (M.op y y) ∨ x = (M.op x y) ∨ (M.op (M.op y y) (M.op y y)) = (k (M.op y y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (M.op y y) x
       have i₂ := eq7407
       grind)
    | exact superpose eq7407 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq7407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7407
  have eq8730 : (M.op x y) ≠ (M.op y y) ∨ x = (M.op x y) ∨ (M.op (M.op y y) (M.op y y)) = (k (M.op y y) x) := by grind
  clear eq8710
  have eq8738 : x = (M.op x y) ∨ (M.op (M.op y y) (M.op y y)) = (k (M.op y y) x) := by
    first
    | (have r₁ := eq8730
       have r₂ := eq5292
       grind)
    | exact resolve eq8730 eq5292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5292 eq8730
  have eq8740 : y = (k (M.op y y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8738
       have i₂ := eq52 y y y
       grind)
    | (have i₁ := eq8738
       have i₂ := eq52 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq52 eq8738
    | exact resolve eq8738 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq8738
  have eq10288 : y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8740
       have i₂ := eq3372
       grind)
    | exact superpose eq3372 eq8740
    | exact resolve eq8740 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372 eq8740
  have eq10302 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq10288
  have eq10348 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq622 x y
       have i₂ := eq10302
       grind)
    | exact superpose eq10302 eq622
    | (have j0 := eq622 x y
       grind)
    | exact resolve eq622 eq10302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq10302
  have eq10353 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10348
  have eq10359 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10353
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10353
    | exact resolve eq10353 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10353
  have eq10370 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10359
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10359
    | exact resolve eq10359 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10359
  have eq10377 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10370
    | exact resolve eq10370 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10370
  have eq10384 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10377
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10377
    | exact resolve eq10377 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10377
  have eq10391 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10384
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10384
    | exact resolve eq10384 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10384
  have eq10398 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10391
    | exact resolve eq10391 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10391
  have eq11178 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10398 eq27
    | exact resolve eq27 eq10398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10398
  have eq11231 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11178
       have r₂ := eq3087
       grind)
    | exact resolve eq11178 eq3087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11178
  have eq11260 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11231 eq3480
    | exact resolve eq3480 eq11231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480 eq11231
  have eq11267 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11260
  have eq11279 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11267
    | exact resolve eq11267 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11267
  have eq11282 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11279 eq27
    | exact resolve eq27 eq11279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11279
  have eq11337 : x = (M.op x y) := by
    first
    | (have r₁ := eq11282
       have r₂ := eq3087
       grind)
    | exact resolve eq11282 eq3087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3087 eq11282
  have eq11339 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq11337 eq20
    | exact resolve eq20 eq11337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq11342 : x ≠ x ∨ (k y x) = (M.op x x) := by
    first
    | exact superpose eq11337 eq66
    | (have r₁ := eq66
       have r₂ := eq11337
       grind)
    | exact resolve eq66 eq11337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq11347 : x = (M.op (M.op x x) x) := by
    first
    | exact superpose eq11337 eq214
    | exact resolve eq214 eq11337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq11370 : (k y x) = (M.op x x) := by grind
  clear eq11342
  have eq11382 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11339
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11339
    | exact resolve eq11339 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11339
  have eq11383 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11382 eq26
    | exact resolve eq26 eq11382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11398 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq11382 eq273
    | exact resolve eq273 eq11382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq11476 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq272 (M.op x x)
       have i₂ := eq11347
       grind)
    | exact superpose eq11347 eq272
    | exact resolve eq272 eq11347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq11347
  have eq11506 : x = (M.op x x) := by
    first
    | exact superpose eq11337 eq11476
    | exact resolve eq11476 eq11337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11337 eq11476
  have eq11511 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq11506
       grind)
    | exact superpose eq11506 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq11506
       grind)
    | exact resolve eq13 eq11506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11539 : x = (k x x) := by grind
  clear eq11511
  have eq11557 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq628 x x
       have i₂ := eq11539
       grind)
    | exact superpose eq11539 eq628
    | (have j0 := eq628 x x
       grind)
    | exact resolve eq628 eq11539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq11539
  have eq11558 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11557
  have eq11559 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11558
  have eq11571 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11559
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11559
    | exact resolve eq11559 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11559
  have eq11580 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11382 eq11571
    | exact resolve eq11571 eq11382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11571
  have eq11998 : x = (k y x) := by
    first
    | (have i₁ := eq11370
       have i₂ := eq11506
       grind)
    | exact superpose eq11506 eq11370
    | exact resolve eq11370 eq11506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11370 eq11506
  have eq12012 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq623 x y
       have i₂ := eq11998
       grind)
    | exact superpose eq11998 eq623
    | (have j0 := eq623 x y
       grind)
    | exact resolve eq623 eq11998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq11998
  have eq12015 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12012
  have eq12021 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12015
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12015
    | exact resolve eq12015 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12015
  have eq12032 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12021
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12021
    | exact resolve eq12021 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12021
  have eq12040 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12032
    | exact resolve eq12032 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12032
  have eq12048 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12040
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12040
    | exact resolve eq12040 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq12040
  have eq12055 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12048
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12048
    | exact resolve eq12048 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12048
  have eq12062 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12055
    | exact resolve eq12055 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12055
  have eq12069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11382 eq12062
    | exact resolve eq12062 eq11382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11382 eq12062
  have eq12076 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12069
       have r₂ := eq27
       grind)
    | exact resolve eq12069 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12069
  have eq12200 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq12076 eq11398
    | exact resolve eq11398 eq12076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11398 eq12076
  have eq12365 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11580 eq12200
    | exact resolve eq12200 eq11580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11580 eq12200
  have eq12403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11383 eq12365
    | exact resolve eq12365 eq11383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11383 eq12365
  have eq12407 : False := by grind
  exact eq12407

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq243 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq85 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq85 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq85 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq253 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq243 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq254 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq253 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq254
    | (have j0 := eq254 X0 X1
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq260 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq256 X0 X1
       have j1 := eq252 X1 X0
       grind)
    | (have r₁ := eq256 X1 X0
       have r₂ := eq252 X0 X1
       grind)
    | (have r₁ := eq256 (k X1 X0) X1
       have r₂ := eq252 X0 X1
       grind)
    | (have r₁ := eq256 X1 X1
       have r₂ := eq252 X1 X1
       grind)
    | exact resolve eq256 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq256
  have eq628 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq260 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq260
    | exact resolve eq260 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq260 y x
       grind)
    | exact superpose eq260 eq16
    | (have j1 := eq260 y x
       grind)
    | exact resolve eq16 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq665 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq628
    | (have j0 := eq628 X0 X1
       grind)
    | exact resolve eq628 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq628
  have eq670 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq665
    | exact resolve eq665 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq743 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq670 (τ X1) X0
       grind)
    | exact superpose eq670 eq18
    | (have j1 := eq670 (τ X1) X0
       grind)
    | exact resolve eq18 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq670
  have eq965 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq743 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq743
    | exact resolve eq743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq1019 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq965 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq965
    | (have j0 := eq965 X0 X1
       grind)
    | exact resolve eq965 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq1117 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq642
       have i₂ := eq1019 y x
       grind)
    | exact superpose eq1019 eq642
    | (have j1 := eq1019 (σ y) (σ x)
       grind)
    | (have r₁ := eq642
       have r₂ := eq1019 y x
       grind)
    | exact resolve eq642 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1118 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1117
  have eq1173 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1118
  have eq1235 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq642
       have i₂ := eq1173
       grind)
    | exact superpose eq1173 eq642
    | exact resolve eq642 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq1173
  have eq1236 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1235
  have eq1237 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1236
  have eq1253 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1237
  have eq1267 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1253
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1253
    | exact resolve eq1253 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1542 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq16
    | exact resolve eq16 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1592 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1542
       have i₂ := eq1019 y x
       grind)
    | exact superpose eq1019 eq1542
    | (have j1 := eq1019 y x
       grind)
    | (have r₁ := eq1542
       have r₂ := eq1019 y x
       grind)
    | exact resolve eq1542 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1593 : y = (M.op x x) := by grind
  clear eq1592
  have eq1600 : (M.op x y) = (k y x) := by grind
  clear eq1593
  have eq1690 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1542
       have i₂ := eq1600
       grind)
    | exact superpose eq1600 eq1542
    | exact resolve eq1542 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542 eq1600
  have eq1693 : False := by grind
  exact eq1693

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  clear eq19
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
  have eq63 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq344 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  have eq347 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq722 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X2 (σ X1) (σ X0)
       have i₂ := eq347 X1 X0
       grind)
    | exact superpose eq347 eq63
    | (have j1 := eq347 X1 X0
       grind)
    | exact resolve eq63 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (σ X1) (σ X0) X2
       have i₂ := eq347 X1 X0
       grind)
    | exact superpose eq347 eq63
    | (have j1 := eq347 X1 X0
       grind)
    | exact resolve eq63 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (M.op (σ (k X0 X1)) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (σ X0) (σ X1) x
       have i₂ := eq347 X0 X1
       grind)
    | exact superpose eq347 eq64
    | (have j1 := eq347 X1 X0
       grind)
    | exact resolve eq64 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq74 (σ x)
       have i₂ := eq347 x x
       grind)
    | exact superpose eq347 eq74
    | (have j1 := eq347 X0 X0
       grind)
    | exact resolve eq74 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq738 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq743 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq738 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq738
    | (have j0 := eq738 X0
       grind)
    | exact resolve eq738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq3086 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    grind
  clear eq743
  have eq3088 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3086 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3086
    | (have j0 := eq3086 X0
       grind)
    | exact resolve eq3086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq3147 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq344 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq344
    | exact resolve eq344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq3196 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3147 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3147
    | (have j0 := eq3147 X0 X1
       grind)
    | exact resolve eq3147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3147
  have eq3502 : ∀ X0 X1 X2 : G, (k (τ X2) (k X1 X0)) = (τ (k X2 (σ (M.op X0 X1)))) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (k X1 X0)
       have i₂ := eq3196 X0 X1
       grind)
    | exact superpose eq3196 eq24
    | (have j1 := eq3196 X0 X1
       grind)
    | exact resolve eq24 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3531 : ∀ X0 X1 X2 : G, (k (τ X2) (k X1 X0)) = (k (τ X2) (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3502 X0 X1 X2
       have i₂ := eq24 X2 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq3502
    | (have j0 := eq3502 X0 X1 X2
       grind)
    | exact resolve eq3502 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3502
  have eq7177 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (M.op X2 X1)) ∨ (M.op X1 X1) = X2 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3531 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3531
    | (have j0 := eq3531 X2 X1 X2
       grind)
    | exact resolve eq3531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3531
  have eq11574 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq74 (σ X0)
       have i₂ := eq3088 X0
       grind)
    | exact superpose eq3088 eq74
    | (have j1 := eq3088 X0
       grind)
    | exact resolve eq74 eq3088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3088
  have eq11617 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11574 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq11574
    | (have j0 := eq11574 X0
       grind)
    | exact resolve eq11574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11574
  have eq11618 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq11617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11617
  have eq11664 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) (σ (τ X0))) = (σ (k (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11618 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq11618
    | exact resolve eq11618 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11711 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (M.op X1 (σ (k X0 X0))) (σ (k X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ (k X0 X0)) (σ X0)
       have i₂ := eq11618 X0
       grind)
    | exact superpose eq11618 eq63
    | exact resolve eq63 eq11618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11712 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 (k X0 X0))) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ (k X0 X0)) (σ X0) X1
       have i₂ := eq11618 X0
       grind)
    | exact superpose eq11618 eq63
    | exact resolve eq63 eq11618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11618
  have eq11758 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) (σ (τ X0))) = (k (σ (τ X0)) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11664 X0
       have i₂ := eq20 (k X0 X0) (τ X0)
       grind)
    | exact superpose eq20 eq11664
    | exact resolve eq11664 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11664
  have eq11792 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (σ (τ (k X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq11758 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11758
    | exact resolve eq11758 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11758
  have eq11814 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11792 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq11792
    | exact resolve eq11792 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11792
  have eq11877 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7177 X0 X0 X0
       have i₂ := eq11814 X0
       grind)
    | exact superpose eq11814 eq7177
    | (have j0 := eq7177 X0 X0 X0
       grind)
    | exact resolve eq7177 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7177
  have eq11924 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11877 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11877
  have eq11972 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11924 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq11924
    | (have j0 := eq11924 X0
       grind)
    | exact resolve eq11924 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11924
  have eq12145 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (k X0 X0) X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11712 X0 X1
       have i₂ := eq11814 X0
       grind)
    | exact superpose eq11814 eq11712
    | exact resolve eq11712 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11712
  have eq12590 : ∀ X0 X1 : G, (σ (M.op (k X0 X0) X0)) = (M.op (M.op X1 (σ (M.op (k X0 X0) X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ (M.op (k X0 X0) X0)) (M.op (σ X0) x)
       have i₂ := eq12145 X0 x
       grind)
    | exact superpose eq12145 eq63
    | exact resolve eq63 eq12145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12145
  have eq12793 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (k X0 X0) X0
       have i₂ := eq11972 X0
       grind)
    | exact superpose eq11972 eq63
    | (have j1 := eq11972 X0
       grind)
    | exact resolve eq63 eq11972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq11972
  have eq13364 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op X2 (σ (τ X1))) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq722 (τ X0) (τ X1) X2
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq722
    | (have j0 := eq722 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq722 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq13453 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op X2 (σ (τ X1))) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13364 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq13364
    | (have j0 := eq13364 X0 X1 X2
       grind)
    | exact resolve eq13364 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13364
  have eq13495 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13453 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13453
    | (have j0 := eq13453 X0 X1 X2
       grind)
    | exact resolve eq13453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13453
  have eq13529 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13495 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13495
    | (have j0 := eq13495 X0 X1 X2
       grind)
    | exact resolve eq13495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13495
  have eq13557 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13529 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq13529
    | (have j0 := eq13529 X0 X1 X2
       grind)
    | exact resolve eq13529 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13529
  have eq13577 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X2 X1) (k X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13557 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13557
    | (have j0 := eq13557 X0 X1 X2
       grind)
    | exact resolve eq13557 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13557
  have eq13592 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13577 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13577
    | (have j0 := eq13577 X0 X1 X2
       grind)
    | exact resolve eq13577 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13577
  have eq13964 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (M.op X1 (σ (k X0 X0))) (σ (M.op (k X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11711 X0 X1
       have i₂ := eq11814 X0
       grind)
    | exact superpose eq11814 eq11711
    | exact resolve eq11711 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11711 eq11814
  have eq15266 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq12590 X0 (M.op x (σ (k X0 X0)))
       have i₂ := eq13964 X0 x
       grind)
    | exact superpose eq13964 eq12590
    | exact resolve eq12590 eq13964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12590 eq13964
  have eq18353 : ∀ X0 : G, (k X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12793 X0 (M.op x X0)
       have i₂ := eq13592 X0 X0 x
       grind)
    | exact superpose eq13592 eq12793
    | (have j0 := eq12793 X0 x
       have j1 := eq13592 X0 X0 x
       grind)
    | exact resolve eq12793 eq13592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12793 eq13592
  have eq18409 : ∀ X0 : G, (k X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq18353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18353
  have eq18413 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq18409 X0
       have i₂ := eq64 X0 X0 X0
       grind)
    | (have i₁ := eq18409 X0
       have i₂ := eq64 X0 (M.op (M.op X0 X0) X0) x
       grind)
    | exact superpose eq64 eq18409
    | (have j0 := eq18409 X0
       grind)
    | exact resolve eq18409 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq18409
  have eq18429 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq18413 X0
       grind)
    | exact superpose eq18413 eq74
    | (have j1 := eq18413 X0
       grind)
    | exact resolve eq74 eq18413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq18413
  have eq18492 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18429
  have eq18604 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15266 X0
       have i₂ := eq18492 X0
       grind)
    | exact superpose eq18492 eq15266
    | exact resolve eq15266 eq18492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15266
  have eq18641 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq18492 (σ X0)
       grind)
    | exact superpose eq18492 eq15
    | exact resolve eq15 eq18492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18648 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq18492 (τ X0)
       grind)
    | exact superpose eq18492 eq33
    | exact resolve eq33 eq18492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq18702 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18648 X0
       have i₂ := eq18492 X0
       grind)
    | exact superpose eq18492 eq18648
    | exact resolve eq18648 eq18492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18648
  have eq18709 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18641 X0
       have i₂ := eq18492 X0
       grind)
    | exact superpose eq18492 eq18641
    | exact resolve eq18641 eq18492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18492 eq18641
  have eq18959 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (k (σ X0) X1) (M.op (σ X0) X2)) ∨ (σ (τ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq723 X0 (τ X1) X2
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq723
    | (have j0 := eq723 X0 (τ X1) X2
       grind)
    | exact resolve eq723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq19141 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (k (σ X0) X1) (M.op (σ X0) X2)) ∨ (σ X0) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18959 X0 X1 X2
       have i₂ := eq18709 X0
       grind)
    | exact superpose eq18709 eq18959
    | (have j0 := eq18959 X0 X1 X2
       grind)
    | exact resolve eq18959 eq18709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18959
  have eq19231 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op (k (σ X0) X1) (M.op (σ X0) X2)) ∨ (σ X0) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19141 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19141
    | (have j0 := eq19141 X0 X1 X2
       grind)
    | exact resolve eq19141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19141
  have eq19309 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op (k (σ X0) X1) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19231 X0 X1 X2
       have i₂ := eq18709 (τ X1)
       grind)
    | exact superpose eq18709 eq19231
    | (have j0 := eq19231 X0 X1 X2
       grind)
    | exact resolve eq19231 eq18709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19231
  have eq19377 : ∀ X0 X1 X2 : G, (σ X0) = (σ (τ (M.op X1 X1))) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op (k (σ X0) X1) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19309 X0 X1 X2
       have i₂ := eq18702 X1
       grind)
    | exact superpose eq18702 eq19309
    | (have j0 := eq19309 X0 X1 X2
       grind)
    | exact resolve eq19309 eq18702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19309
  have eq19429 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (k (σ X0) X1) (M.op (σ X0) X2)) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19377 X0 X1 X2
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq19377
    | (have j0 := eq19377 X0 X1 X2
       grind)
    | exact resolve eq19377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19377
  have eq19909 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq19982 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19909 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq19909
    | exact resolve eq19909 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19909
  have eq20046 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq19982
  have eq26924 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ (τ X1)) (M.op (k (σ X0) X1) X2)) ∨ (σ (τ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq724 X1 (τ X0) X2
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq724
    | (have j0 := eq724 X0 (τ X1) X2
       grind)
    | exact resolve eq724 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq724
  have eq27065 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op X1 (M.op (k (σ X0) X1) X2)) ∨ (σ (τ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26924 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq26924
    | (have j0 := eq26924 X0 X1 X2
       grind)
    | exact resolve eq26924 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26924
  have eq27160 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (M.op (k (σ X0) X1) X2)) ∨ (σ X0) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27065 X0 X1 X2
       have i₂ := eq18709 X0
       grind)
    | exact superpose eq18709 eq27065
    | (have j0 := eq27065 X0 X1 X2
       grind)
    | exact resolve eq27065 eq18709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27065
  have eq27227 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (M.op (k (σ X0) X1) X2)) ∨ (σ X0) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27160 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27160
    | (have j0 := eq27160 X0 X1 X2
       grind)
    | exact resolve eq27160 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27160
  have eq27283 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (M.op (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27227 X0 X1 X2
       have i₂ := eq18709 (τ X1)
       grind)
    | exact superpose eq18709 eq27227
    | (have j0 := eq27227 X0 X1 X2
       grind)
    | exact resolve eq27227 eq18709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27227
  have eq27327 : ∀ X0 X1 X2 : G, (σ X0) = (σ (τ (M.op X1 X1))) ∨ (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (M.op (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27283 X0 X1 X2
       have i₂ := eq18702 X1
       grind)
    | exact superpose eq18702 eq27283
    | (have j0 := eq27283 X0 X1 X2
       grind)
    | exact resolve eq27283 eq18702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18702 eq27283
  have eq27369 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op X1 (M.op (k (σ X0) X1) X2)) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27327 X0 X1 X2
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq27327
    | (have j0 := eq27327 X0 X1 X2
       grind)
    | exact resolve eq27327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27327
  have eq101250 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27369 X0 X1 (M.op (σ X0) x)
       have i₂ := eq19429 X0 X1 x
       grind)
    | exact superpose eq19429 eq27369
    | (have j0 := eq27369 X0 X1 x
       have j1 := eq19429 X0 X1 x
       grind)
    | exact resolve eq27369 eq19429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19429 eq27369
  have eq101368 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq101250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101250
  have eq101745 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq101368 X1 (σ X0)
       grind)
    | exact superpose eq101368 eq15
    | (have j1 := eq101368 X1 (σ X0)
       grind)
    | exact resolve eq15 eq101368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101368
  have eq101943 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101745 X0 X1
       have i₂ := eq18709 X0
       grind)
    | exact superpose eq18709 eq101745
    | (have j0 := eq101745 X0 X1
       grind)
    | exact resolve eq101745 eq18709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18709 eq101745
  have eq137354 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101943 x y
       grind)
    | exact superpose eq101943 eq16
    | (have j1 := eq101943 x y
       grind)
    | exact resolve eq16 eq101943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101943
  have eq141275 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq137354
       have i₂ := eq3196 x y
       grind)
    | exact superpose eq3196 eq137354
    | (have j1 := eq3196 x y
       grind)
    | (have r₁ := eq137354
       have r₂ := eq3196 x y
       grind)
    | exact resolve eq137354 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196 eq137354
  have eq141276 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq141275
  have eq155320 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq141276
       grind)
    | exact superpose eq141276 eq10
    | exact resolve eq10 eq141276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141276
  have eq155682 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq155320
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq155320
    | exact resolve eq155320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155320
  have eq155683 : (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq155682
  have eq156240 : (M.op y y) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq155683
       grind)
    | exact superpose eq155683 eq10
    | exact resolve eq10 eq155683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155683
  have eq156604 : x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq156240
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq156240
    | exact resolve eq156240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156240
  have eq156605 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq156604
  have eq156810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq20046 x
       have i₂ := eq156605
       grind)
    | exact superpose eq156605 eq20046
    | exact resolve eq20046 eq156605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20046 eq156605
  have eq156970 : x = (M.op y y) := by
    first
    | (have r₁ := eq156810
       have r₂ := eq16
       grind)
    | exact resolve eq156810 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156810
  have eq157082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18604 y
       have i₂ := eq156970
       grind)
    | exact superpose eq156970 eq18604
    | exact resolve eq18604 eq156970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18604 eq156970
  have eq157273 : False := by grind
  exact eq157273
