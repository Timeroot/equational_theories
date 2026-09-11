import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq117 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | (have r₁ := eq117 X0 X1
       have r₂ := eq44 X0 X1
       grind)
    | (have r₁ := eq117 X0 X0
       have r₂ := eq44 X0 X0
       grind)
    | exact resolve eq117 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq117
  have eq223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq121 (σ X0) (σ X1)
       grind)
    | exact superpose eq121 eq15
    | exact resolve eq15 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq223
    | exact resolve eq223 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq223
  have eq232 : False := by grind
  exact eq232

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq175 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq176 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X0 X1 X2 X3
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq180 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq181 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op (M.op X2 X1) X0) X0) = (k (M.op (M.op X2 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq16 X1 y X0
       grind)
    | exact superpose eq16 eq186
    | exact resolve eq186 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq193 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 x X0
       have i₂ := eq16 X0 sF3 x
       grind)
    | exact superpose eq16 eq193
    | exact resolve eq193 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq399 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq598 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (k X0 X1) X2)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq607 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq607 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq607 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq646 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq598
       grind)
    | exact superpose eq598 eq41
    | exact resolve eq41 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq647 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq646
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq646
    | exact resolve eq646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq649 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq647
    | exact resolve eq647 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq649 eq599
    | exact resolve eq599 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq657
       have r₂ := eq27
       grind)
    | exact resolve eq657 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq668 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq664 eq181
    | (have r₁ := eq181
       have r₂ := eq664
       grind)
    | exact resolve eq181 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq669 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq664 eq196
    | exact resolve eq196 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq668
  have eq676 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq669
    | (have j0 := eq669 X0 (σ y)
       grind)
    | exact resolve eq669 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq700 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq664 eq676
    | exact resolve eq676 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq711 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq700 eq26
    | (have j1 := eq700 (σ x)
       grind)
    | exact resolve eq26 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq716 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq664 eq711
    | exact resolve eq711 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq724 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq716 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq716
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq716
       grind)
    | exact resolve eq13 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq726 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq724
  have eq737 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ (k x y) = (M.op y x) := by
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
  have eq738 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq623 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq623
    | (have j0 := eq623 (σ X0) (σ X1)
       grind)
    | exact resolve eq623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq726 eq142
    | exact resolve eq142 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq726
  have eq752 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq749
    | exact resolve eq749 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq749
  have eq757 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq623 x x
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq623
    | (have j0 := eq623 x x
       grind)
    | (have r₁ := eq623 x x
       have r₂ := eq752
       grind)
    | exact resolve eq623 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq758 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq757
  have eq762 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 x X0 x
       have i₂ := eq758
       grind)
    | exact superpose eq758 eq179
    | exact resolve eq179 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq762 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq762
    | (have j0 := eq762 X0 y
       grind)
    | exact resolve eq762 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq946 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq758
       have i₂ := eq893 x
       grind)
    | exact superpose eq893 eq758
    | exact resolve eq758 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq961 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq946
  have eq2269 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq664 eq738
    | (have r₁ := eq738
       have r₂ := eq664
       grind)
    | exact resolve eq738 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq738
  have eq2270 : (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2269
  have eq2271 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq649 eq2270
    | exact resolve eq2270 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq2402 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2271 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2271
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2271
       grind)
    | exact resolve eq13 eq2271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271
  have eq2405 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2402
  have eq2414 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2405
    | exact resolve eq2405 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2421 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq649 eq2414
    | exact resolve eq2414 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq2414
  have eq2423 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2421
       have r₂ := eq27
       grind)
    | exact resolve eq2421 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq2428 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2423 eq672
    | exact resolve eq672 eq2423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq2423
  have eq2438 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2428
  have eq2450 : (τ (σ (M.op x y))) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2438 eq115
    | exact resolve eq115 eq2438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq2438
  have eq2466 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2450
    | exact resolve eq2450 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2450
  have eq2556 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op X0 x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq608 y x X0
       have i₂ := eq2466
       grind)
    | exact superpose eq2466 eq608
    | (have j0 := eq608 y x x
       grind)
    | exact resolve eq608 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466
  have eq2564 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq175 eq2556
    | exact resolve eq2556 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2556
  have eq2567 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq893 eq2564
    | exact resolve eq2564 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2564
  have eq3481 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2567 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq2567 x
       grind)
    | exact superpose eq2567 eq18
    | (have j1 := eq2567 x
       grind)
    | exact resolve eq18 eq2567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567
  have eq3512 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq961 eq3481
    | exact resolve eq3481 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3481
  have eq3513 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq3512
  have eq3524 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq893 y
       have i₂ := eq3513
       grind)
    | exact superpose eq3513 eq893
    | exact resolve eq893 eq3513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3530 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 x X0 y
       have i₂ := eq3513
       grind)
    | exact superpose eq3513 eq179
    | exact resolve eq179 eq3513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3513
  have eq3536 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3524
  have eq3540 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op y X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq893 eq3530
    | exact resolve eq3530 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq3530
  have eq3583 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3536 eq3540
    | exact resolve eq3540 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536 eq3540
  have eq3692 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3583 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3583
  have eq3724 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3692 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq3692 x
       grind)
    | exact superpose eq3692 eq18
    | (have j1 := eq3692 x
       grind)
    | exact resolve eq18 eq3692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3692
  have eq3773 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3724 eq961
    | exact resolve eq961 eq3724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq3724
  have eq3792 : x = (M.op x y) := by grind
  clear eq3773
  have eq3798 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3792
       grind)
    | exact superpose eq3792 eq18
    | exact resolve eq18 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3799 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq3792
       grind)
    | exact superpose eq3792 eq22
    | exact resolve eq22 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3801 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq3792
       grind)
    | exact superpose eq3792 eq40
    | exact resolve eq40 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq3802 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq3792
       grind)
    | exact superpose eq3792 eq180
    | (have r₁ := eq180
       have r₂ := eq3792
       grind)
    | exact resolve eq180 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq3803 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ (k (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq737
       have i₂ := eq3792
       grind)
    | exact superpose eq3792 eq737
    | (have r₁ := eq737
       have r₂ := eq3792
       grind)
    | exact resolve eq737 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq3792
  have eq3804 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq3803
  have eq3805 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
  clear eq3802
  have eq3807 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3799 eq20
    | exact resolve eq20 eq3799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3818 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq3799 eq399
    | exact resolve eq399 eq3799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq3799
  have eq3879 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3798 eq188
    | exact resolve eq188 eq3798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq3907 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (k y (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq3805 eq179
    | exact resolve eq179 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3939 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3798
       have i₂ := eq3879 sF0
       grind)
    | exact superpose eq3879 eq3798
    | exact resolve eq3798 eq3879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3798
  have eq3969 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3939 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq3939
       grind)
    | exact resolve eq13 eq3939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3977 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq3969
  have eq3986 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3977 eq38
    | exact resolve eq38 eq3977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3977
  have eq4000 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3986
    | exact resolve eq3986 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3986
  have eq4002 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3807 eq4000
    | exact resolve eq4000 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4000
  have eq4011 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4002 eq623
    | (have j0 := eq623 (σ x) (σ x)
       grind)
    | (have r₁ := eq623 (σ x) (σ x)
       have r₂ := eq4002
       grind)
    | exact resolve eq623 eq4002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4002
  have eq4012 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4011
  have eq4034 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq4012 eq179
    | exact resolve eq179 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4035 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) = (k (M.op (M.op X0 (σ x)) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq4012 eq182
    | (have j0 := eq182 (σ x) (σ x) X0
       grind)
    | (have r₁ := eq182 (σ x) (σ x) x
       have r₂ := eq4012
       grind)
    | exact resolve eq182 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq4037 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) = (k (M.op (M.op X0 (σ x)) (σ x)) (σ x)) := by
    intro X0
    first
    | (have j0 := eq4035 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035
  have eq4268 : (k (M.op x y) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq599 eq3818
    | exact resolve eq3818 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3818
  have eq4324 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq4268
    | exact resolve eq4268 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4268
  have eq4454 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq4034
    | (have j0 := eq4034 X0 (σ y)
       grind)
    | exact resolve eq4034 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4498 : ∀ X0 X1 : G, (M.op X0 (σ x)) ≠ X0 ∨ (M.op (M.op (σ x) X1) X0) = (k (M.op (σ x) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq4034 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | exact resolve eq13 eq4034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034
  have eq4633 : ∀ X0 : G, (M.op X0 (σ x)) ≠ X0 ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq4454 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | exact resolve eq13 eq4454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4730 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (k X0 (M.op (k y (M.op x y)) X1)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq3907 eq28
    | (have j0 := eq28 X0 (M.op x y)
       grind)
    | exact resolve eq28 eq3907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907
  have eq4768 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (k X0 (M.op (k y (M.op x y)) X1)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq28 eq4730
    | (have j0 := eq4730 X0 X1
       have j1 := eq28 X0 (M.op x y)
       grind)
    | exact resolve eq4730 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4730
  have eq4853 : (k (M.op x y) y) = (k y (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq3805 eq3804
    | exact resolve eq3804 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4867 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (k (M.op x y) y) X1)) ∨ y = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq3804 eq179
    | exact resolve eq179 eq3804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3804
  have eq4874 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (k (M.op x y) y) X1)) ∨ y = (k y (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq3805 eq4867
    | (have j0 := eq4867 X0 X1
       grind)
    | exact resolve eq4867 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4867
  have eq4938 : (k (σ y) (σ x)) = (σ (k (M.op x y) y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq4853 eq3801
    | exact resolve eq3801 eq4853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3801
  have eq4950 : (k (σ y) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq4938
       have i₂ := eq41 sF0
       grind)
    | exact superpose eq41 eq4938
    | exact resolve eq4938 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4938
  have eq4957 : (k (σ y) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq20 eq4950
    | exact resolve eq4950 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4950
  have eq4961 : (k (σ y) (σ x)) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq3807 eq4957
    | exact resolve eq4957 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957
  have eq4964 : (k (σ y) (σ x)) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq4961
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4961
    | exact resolve eq4961 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4961
  have eq5154 : (σ x) ≠ (σ x) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq4012 eq4633
    | (have j0 := eq4633 (σ x)
       grind)
    | (have r₁ := eq4633 (σ x)
       have r₂ := eq4012
       grind)
    | exact resolve eq4633 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4633
  have eq5165 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq5154
  have eq5169 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq5165 eq196
    | exact resolve eq196 eq5165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq5165
  have eq9484 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X1 (k (M.op (M.op X0 (σ x)) (σ x)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq4037 eq179
    | exact resolve eq179 eq4037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9514 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X1 (k (k (M.op (M.op X0 (σ x)) (σ x)) (σ x)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq4037 eq9484
    | exact resolve eq9484 eq4037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4037 eq9484
  have eq10475 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (τ (M.op (σ x) (σ y))) X1)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq4324 eq4874
    | exact resolve eq4874 eq4324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4874
  have eq10682 : ∀ X0 : G, (σ (k y (M.op x y))) = (k (σ y) (σ (M.op (k y (M.op x y)) X0))) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4768 eq37
    | (have j1 := eq4768 y x
       grind)
    | exact resolve eq37 eq4768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4768
  have eq10697 : ∀ X0 : G, (k (σ y) (σ (M.op x y))) = (k (σ y) (σ (M.op (k y (M.op x y)) X0))) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq42 eq10682
    | exact resolve eq10682 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq10682
  have eq10710 : ∀ X0 : G, (k (σ y) (σ x)) = (k (σ y) (σ (M.op (k y (M.op x y)) X0))) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3807 eq10697
    | exact resolve eq10697 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10697
  have eq10718 : ∀ X0 : G, (k (σ y) (σ x)) = (k (σ y) (σ (M.op (k y (M.op x y)) X0))) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq10710 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10710
    | (have j0 := eq10710 X0
       grind)
    | exact resolve eq10710 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10710
  have eq10723 : ∀ X0 : G, y = (k y (M.op x y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ (M.op (k y (M.op x y)) X0))) := by
    intro X0
    first
    | exact superpose eq3805 eq10718
    | (have j0 := eq10718 X0
       grind)
    | exact resolve eq10718 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10718
  have eq10727 : ∀ X0 : G, y = (k y (M.op x y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ (M.op (k (M.op x y) y) X0))) := by
    intro X0
    first
    | exact superpose eq4853 eq10723
    | exact resolve eq10723 eq4853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4853 eq10723
  have eq10731 : ∀ X0 : G, (k (σ x) (σ y)) = (k (σ y) (σ (M.op (k (M.op x y) y) X0))) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4964 eq10727
    | exact resolve eq10727 eq4964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10727
  have eq11887 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (M.op (σ x) X0) (σ x)) = (k (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq4012 eq4498
    | (have j0 := eq4498 (σ x) X0
       grind)
    | (have r₁ := eq4498 (σ x) x
       have r₂ := eq4012
       grind)
    | exact resolve eq4498 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4498
  have eq11899 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (k (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq11887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11887
  have eq11970 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (M.op (σ x) X0) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq11899 eq179
    | exact resolve eq179 eq11899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq11899
  have eq12078 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (k (M.op (σ x) X1) (σ x))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq11970 eq28
    | (have j0 := eq28 X0 X1
       grind)
    | exact resolve eq28 eq11970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11970
  have eq12139 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k (M.op (σ x) X1) (σ x))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq28 eq12078
    | (have j0 := eq12078 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | exact resolve eq12078 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12078
  have eq13915 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ (k (M.op (σ x) X0) (σ x)))) ∨ y = (M.op y X0) := by
    intro X0
    first
    | exact superpose eq12139 eq37
    | (have j1 := eq12139 y X0
       grind)
    | exact resolve eq37 eq12139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12139
  have eq13940 : ∀ X0 : G, (k (σ y) (σ X0)) = (k (σ y) (σ (k (M.op (σ x) X0) (σ x)))) ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13915 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq13915
    | (have j0 := eq13915 X0
       grind)
    | exact resolve eq13915 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq13915
  have eq20467 : ∀ X0 : G, (k (σ x) (σ y)) = (k (σ y) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4324 eq10731
    | exact resolve eq10731 eq4324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4324 eq10731
  have eq20572 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq599 eq20467
    | exact resolve eq20467 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20467
  have eq75237 : ∀ X0 : G, (k (σ y) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) = (k (σ y) (σ (k (M.op (σ x) (M.op x y)) (σ x)))) ∨ y = (M.op y (M.op (τ (M.op (σ x) (σ y))) X0)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10475 eq13940
    | (have j0 := eq13940 (M.op (τ (M.op (σ x) (σ y))) X0)
       grind)
    | exact resolve eq13940 eq10475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75429 : ∀ X0 : G, (k (σ y) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) = (k (σ y) (σ (k (M.op (σ x) (M.op x y)) (σ x)))) ∨ y = (M.op y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10475 eq75237
    | (have j0 := eq75237 X0
       grind)
    | exact resolve eq75237 eq10475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10475 eq75237
  have eq75494 : ∀ X0 : G, (k (σ y) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) = (k (σ y) (σ (k (M.op (σ x) (M.op x y)) (σ x)))) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq75429 X0
       have j1 := eq623 y (M.op x y)
       grind)
    | (have r₁ := eq75429 X0
       have r₂ := eq623 y (M.op x y)
       grind)
    | exact resolve eq75429 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75429
  have eq75551 : ∀ X0 : G, y = (k y (M.op x y)) ∨ (k (σ y) (σ (M.op (τ (M.op (σ x) (σ y))) X0))) = (k (σ y) (σ (k (M.op (σ x) (M.op x y)) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3805 eq75494
    | (have j0 := eq75494 X0
       grind)
    | exact resolve eq75494 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75494
  have eq75578 : (M.op (σ x) (σ y)) = (k (σ y) (σ (k (M.op (σ x) (M.op x y)) (σ x)))) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20572 eq75551
    | exact resolve eq75551 eq20572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20572 eq75551
  have eq115003 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75578 eq13940
    | (have j0 := eq13940 (M.op x y)
       grind)
    | exact resolve eq13940 eq75578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13940 eq75578
  have eq115054 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq623 y (M.op x y)
       grind)
    | (have r₁ := eq115003
       have r₂ := eq623 y (M.op x y)
       grind)
    | exact resolve eq115003 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq115003
  have eq115071 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq115054
    | exact resolve eq115054 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115054
  have eq115079 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3807 eq115071
    | exact resolve eq115071 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115071
  have eq115085 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3805 eq115079
    | exact resolve eq115079 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805 eq115079
  have eq115131 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq115085 eq608
    | (have j0 := eq608 (σ y) (σ x) x
       grind)
    | exact resolve eq608 eq115085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq115085
  have eq115146 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq176 eq115131
    | exact resolve eq115131 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq115131
  have eq420374 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115146 eq26
    | (have j1 := eq115146 (σ x)
       grind)
    | exact resolve eq26 eq115146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115146
  have eq420591 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4012 eq420374
    | exact resolve eq420374 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420374
  have eq420592 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq420591
  have eq420789 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (k (M.op (σ y) (σ x)) (σ x)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq420592 eq9514
    | exact resolve eq9514 eq420592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9514
  have eq420920 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (k (σ y) (σ x)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq420592 eq420789
    | exact resolve eq420789 eq420592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420592 eq420789
  have eq420938 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (k (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4964 eq420920
    | exact resolve eq420920 eq4964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4964 eq420920
  have eq420949 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq599 eq420938
    | exact resolve eq420938 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq420938
  have eq420952 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5169 eq420949
    | exact resolve eq420949 eq5169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5169 eq420949
  have eq421647 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq420952 eq26
    | (have j1 := eq420952 (σ x)
       grind)
    | exact resolve eq26 eq420952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420952
  have eq421860 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq4012 eq421647
    | exact resolve eq421647 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4012 eq421647
  have eq421861 : y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq421860
  have eq422139 : y ≠ y ∨ (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq421861 eq632
    | (have j0 := eq632 y (M.op x y)
       grind)
    | (have r₁ := eq632 y (M.op x y)
       have r₂ := eq421861
       grind)
    | exact resolve eq632 eq421861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq421861
  have eq422154 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq422139
  have eq422188 : (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq422154
       have i₂ := eq3879 sF0
       grind)
    | exact superpose eq3879 eq422154
    | exact resolve eq422154 eq3879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3879 eq422154
  have eq422242 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3939 eq422188
    | exact resolve eq422188 eq3939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3939 eq422188
  have eq422645 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq422242 eq742
    | (have j0 := eq742 (M.op x y) y
       grind)
    | exact resolve eq742 eq422242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq422242
  have eq422658 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq422645
  have eq422670 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq422658
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq422658
    | exact resolve eq422658 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq422658
  have eq422702 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq422670
    | exact resolve eq422670 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq422670
  have eq422731 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3807 eq422702
    | exact resolve eq422702 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422702
  have eq422761 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq422731
    | exact resolve eq422731 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq422731
  have eq422762 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq422761
  have eq422779 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq422762 eq27
    | exact resolve eq27 eq422762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq422762
  have eq423013 : False := by grind
  exact eq423013

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq281 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq288 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq288 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq290 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq291 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq294 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq289 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq289 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq289 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq396 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k X0 (M.op (M.op X2 X1) X3)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq291 (M.op (M.op X3 X1) X0) X2
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq291
    | (have j0 := eq291 X1 X0
       grind)
    | exact resolve eq291 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq291 X1 X0
       grind)
    | exact superpose eq291 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq291 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq291 X0 X1
       grind)
    | exact resolve eq13 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq291 (σ y) (σ x)
       grind)
    | exact superpose eq291 eq16
    | (have j1 := eq291 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq399 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq412 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq407
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq415 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq411 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq411 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq411 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq429 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq415 X0 (τ X1)
       grind)
    | exact superpose eq415 eq18
    | (have j1 := eq415 X0 (τ X1)
       grind)
    | exact resolve eq18 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq446 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq415 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op (M.op X2 X1) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq446 X0 (M.op (M.op X2 X1) X3)
       have i₂ := eq63 X3 X1 X0 X2
       grind)
    | exact superpose eq63 eq446
    | (have j0 := eq446 X0 X1
       grind)
    | exact resolve eq446 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X2 X1) X3)) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq454 X0 X1 X2 X3
       have i₂ := eq291 X1 X0
       grind)
    | exact superpose eq291 eq454
    | (have j0 := eq454 X0 X1 X2 X3
       have j1 := eq291 X1 X0
       grind)
    | (have r₁ := eq454 X1 X0 X2 X3
       have r₂ := eq291 X0 X1
       grind)
    | exact resolve eq454 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq646 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 (M.op (M.op X2 X1) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq641 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq1175 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq429 (τ X0) X1
       grind)
    | exact superpose eq429 eq17
    | (have j1 := eq429 (τ X0) X1
       grind)
    | exact resolve eq17 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq429
  have eq1182 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1175 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1175
    | (have j0 := eq1175 X0 X1
       grind)
    | exact resolve eq1175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1195 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1182 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1182
    | (have j0 := eq1182 X0 X1
       grind)
    | exact resolve eq1182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1198 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1195 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1195
    | (have j0 := eq1195 X0 X1
       grind)
    | exact resolve eq1195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1262 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1198 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1198
    | (have j0 := eq1198 X1 (σ X0)
       grind)
    | exact resolve eq1198 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1533 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1262 X0 X0
       have i₂ := eq415 X0 (σ X0)
       grind)
    | exact superpose eq415 eq1262
    | (have j0 := eq1262 X1 X0
       have j1 := eq415 X0 (σ X1)
       grind)
    | exact resolve eq1262 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq1262
  have eq1580 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1533 X0 X1
       have j1 := eq446 X0 (σ X1)
       grind)
    | (have r₁ := eq1533 X0 X1
       have r₂ := eq446 X0 (σ X1)
       grind)
    | exact resolve eq1533 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq1533
  have eq1782 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1580 (σ X0) X1
       grind)
    | exact superpose eq1580 eq28
    | (have j1 := eq1580 (σ X0) X1
       grind)
    | exact resolve eq28 eq1580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1580
  have eq1796 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1782 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1782
    | (have j0 := eq1782 X0 X1
       grind)
    | exact resolve eq1782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq1812 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1796 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1796
    | (have j0 := eq1796 X0 X1
       grind)
    | exact resolve eq1796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq1821 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1812 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1812
    | (have j0 := eq1812 X0 X1
       grind)
    | exact resolve eq1812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812
  have eq1908 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1821 x y
       grind)
    | exact superpose eq1821 eq16
    | (have j1 := eq1821 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1821 x y
       grind)
    | exact resolve eq16 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq1933 : x = (k x y) := by grind
  clear eq1908
  have eq1964 : ∀ X0 X1 : G, x = (M.op x y) ∨ x = (k x (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq646 x y X0 X1
       have i₂ := eq1933
       grind)
    | exact superpose eq1933 eq646
    | (have j0 := eq646 x y X0 X1
       grind)
    | exact resolve eq646 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq1967 : ∀ X0 X1 : G, x = (k x (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1964 X0 X1
       have j1 := eq454 x y X0 X1
       grind)
    | (have r₁ := eq1964 X0 X1
       have r₂ := eq454 x y x x
       grind)
    | exact resolve eq1964 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq1964
  have eq1992 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq396 x y x x
       have i₂ := eq1967 x x
       grind)
    | exact superpose eq1967 eq396
    | (have j0 := eq396 x y x x
       grind)
    | exact resolve eq396 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq1999 : x = (M.op x y) := by grind
  clear eq1992
  have eq2014 : ∀ X0 : G, x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1967 x X0
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq1967
    | exact resolve eq1967 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq2018 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 x
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq63
    | exact resolve eq63 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2028 : x = (k x x) := by
    first
    | (have i₁ := eq2014 y
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq2014
    | exact resolve eq2014 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq2065 : x = (M.op x x) := by
    first
    | (have i₁ := eq2028
       have i₂ := eq294 x
       grind)
    | exact superpose eq294 eq2028
    | exact resolve eq2028 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq2028
  have eq2093 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2018 X0 x
       have i₂ := eq2065
       grind)
    | exact superpose eq2065 eq2018
    | exact resolve eq2018 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq5897 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq412
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq412
    | exact resolve eq412 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq1999
  have eq5905 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq5897
  have eq5913 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5905
       have i₂ := eq1933
       grind)
    | exact superpose eq1933 eq5905
    | exact resolve eq5905 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933 eq5905
  have eq5919 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5913
       grind)
    | exact superpose eq5913 eq16
    | exact resolve eq16 eq5913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5913
  have eq5960 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5919
       have i₂ := eq2093 x
       grind)
    | exact superpose eq2093 eq5919
    | exact resolve eq5919 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093 eq5919
  have eq5965 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5960
       have i₂ := eq2065
       grind)
    | exact superpose eq2065 eq5960
    | exact resolve eq5960 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065 eq5960
  have eq5966 : False := by grind
  exact eq5966

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxx_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq152 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq135
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq135
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq135 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq135 eq16
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq152
  have eq173 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq195 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq210 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq216 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq218 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq216
    | exact resolve eq216 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq901 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3968 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq173 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq173
    | (have j0 := eq173 x
       grind)
    | exact resolve eq173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq3980 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3968
  have eq3985 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3980
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3980
    | exact resolve eq3980 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3980
  have eq4002 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3985
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3985 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3985
  have eq4011 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4002 eq49
    | exact resolve eq49 eq4002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq4214 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq195 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq195
    | (have j0 := eq195 y
       grind)
    | exact resolve eq195 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq4226 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4214
  have eq4230 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4226
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq4226
    | exact resolve eq4226 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq4254 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4230
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4230 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4230
  have eq4480 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq210
    | (have j0 := eq210 (M.op x y)
       grind)
    | exact resolve eq210 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq4490 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq4480
  have eq4493 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq135 eq4490
    | exact resolve eq4490 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq4490
  have eq4524 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq4493
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4493 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4493
  have eq4561 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq4524 eq158
    | exact resolve eq158 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq5632 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq901 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq901
    | (have j0 := eq901 x y
       grind)
    | exact resolve eq901 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5701 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5632
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5632
    | exact resolve eq5632 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5632
  have eq5788 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5701
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5701
    | exact resolve eq5701 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5701
  have eq5875 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5788
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5788
    | exact resolve eq5788 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5788
  have eq5959 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq5875
    | exact resolve eq5875 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5875
  have eq6041 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq5959
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5959
    | exact resolve eq5959 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5959
  have eq6101 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6041
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6041
    | exact resolve eq6041 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6041
  have eq12555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12555
    | exact resolve eq12555 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12555
  have eq12567 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq12556
       have r₂ := eq27
       grind)
    | exact resolve eq12556 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12556
  have eq12569 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12567
    | exact resolve eq12567 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12567
  have eq12572 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12569 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq12569
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12569
       grind)
    | exact resolve eq13 eq12569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12573 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq12569 eq14
    | exact resolve eq14 eq12569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12584 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq12572
  have eq12723 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12584 eq117
    | exact resolve eq117 eq12584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12584
  have eq12736 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12723
  have eq13184 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12569 eq12573
    | exact resolve eq12573 eq12569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12569 eq12573
  have eq13223 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq13184
  have eq13227 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13223
    | exact resolve eq13223 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13223
  have eq13371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13227 eq12736
    | exact resolve eq12736 eq13227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12736
  have eq13383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13371
  have eq13388 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13383
       have r₂ := eq27
       grind)
    | exact resolve eq13383 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13383
  have eq13391 : y ≠ y ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq13388
       grind)
    | exact superpose eq13388 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13388
       grind)
    | exact resolve eq13 eq13388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13392 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq13388
       grind)
    | exact superpose eq13388 eq14
    | exact resolve eq14 eq13388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13403 : (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13391
  have eq13408 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq13403
       grind)
    | exact superpose eq13403 eq44
    | exact resolve eq44 eq13403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13403
  have eq13513 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13392 x
       have i₂ := eq13388
       grind)
    | exact superpose eq13388 eq13392
    | exact resolve eq13392 eq13388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13388 eq13392
  have eq13556 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13513
  have eq13560 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13556
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13556
    | exact resolve eq13556 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13556
  have eq13564 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13408
       have i₂ := eq13560
       grind)
    | exact superpose eq13560 eq13408
    | exact resolve eq13408 eq13560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13408 eq13560
  have eq13576 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13564
  have eq13579 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13576
    | exact resolve eq13576 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13576
  have eq13597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13579 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq13579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13597
    | exact resolve eq13597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13597
  have eq13611 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13600
       have r₂ := eq27
       grind)
    | exact resolve eq13600 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13600
  have eq13613 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13611
    | exact resolve eq13611 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13611
  have eq13614 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13613
  have eq13694 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4524 eq159
    | exact resolve eq159 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq4524
  have eq13697 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13614 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13614
       grind)
    | exact resolve eq13 eq13614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13698 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13614 eq14
    | exact resolve eq14 eq13614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13709 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13697
  have eq13768 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13709 eq13579
    | exact resolve eq13579 eq13709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13579 eq13709
  have eq13775 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13768
  have eq14548 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13614 eq13698
    | exact resolve eq13698 eq13614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13614 eq13698
  have eq14603 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14548
  have eq14607 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14603
    | exact resolve eq14603 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14603
  have eq14620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14607 eq13775
    | exact resolve eq13775 eq14607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13775 eq14607
  have eq14632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14620
  have eq14639 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14632
       have r₂ := eq27
       grind)
    | exact resolve eq14632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14632
  have eq14641 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14639 eq27
    | exact resolve eq27 eq14639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14644 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14639 eq77
    | (have r₁ := eq77
       have r₂ := eq14639
       grind)
    | exact resolve eq77 eq14639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq14639
  have eq14649 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq14644
  have eq14804 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14649 eq58
    | exact resolve eq58 eq14649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14805 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14649 eq117
    | exact resolve eq117 eq14649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14838 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq14805
  have eq14852 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14838
       have r₂ := eq14641
       grind)
    | exact resolve eq14838 eq14641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14838
  have eq14853 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq14804
    | exact resolve eq14804 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14804
  have eq14861 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14852 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14852
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14852
       grind)
    | exact resolve eq13 eq14852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14862 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14852 eq14
    | exact resolve eq14 eq14852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14873 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq14861
  have eq14881 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14853 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14853
       grind)
    | exact resolve eq13 eq14853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14853
  have eq14893 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq14881
  have eq16025 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14873 eq117
    | exact resolve eq117 eq14873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14873
  have eq16054 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq16025
  have eq16481 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq117 eq14893
    | exact resolve eq14893 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq16487 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14893 eq58
    | exact resolve eq58 eq14893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14893
  have eq16520 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq16481
  have eq16527 : (k x x) = (k x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4011 eq16487
    | exact resolve eq16487 eq4011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4011 eq16487
  have eq16528 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq16520
       have r₂ := eq76
       grind)
    | exact resolve eq16520 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16520
  have eq16729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13227 eq16528
    | exact resolve eq16528 eq13227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13227
  have eq16751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16729
  have eq16760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16751
       have r₂ := eq76
       grind)
    | exact resolve eq16751 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16751
  have eq16762 : y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16760
       have r₂ := eq27
       grind)
    | exact resolve eq16760 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16760
  have eq16795 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq901 x y
       have i₂ := eq16762
       grind)
    | exact superpose eq16762 eq901
    | (have j0 := eq901 x y
       grind)
    | exact resolve eq901 eq16762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq16762
  have eq16798 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16795
  have eq16817 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16798
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16798
    | exact resolve eq16798 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq16832 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16817
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16817
    | exact resolve eq16817 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16817
  have eq16839 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16832
    | exact resolve eq16832 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16832
  have eq16840 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq16839
  have eq16845 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16840
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16840
    | exact resolve eq16840 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16840
  have eq16851 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16845
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16845
    | exact resolve eq16845 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16845
  have eq17100 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16851 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq16851
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16851
       grind)
    | exact resolve eq13 eq16851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17112 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq17100
  have eq19986 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14852 eq14862
    | exact resolve eq14862 eq14852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14852 eq14862
  have eq20063 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq19986
  have eq20069 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq20063
    | exact resolve eq20063 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20063
  have eq20090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20069 eq16054
    | exact resolve eq16054 eq20069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16054
  have eq20091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20069 eq16528
    | exact resolve eq16528 eq20069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16528 eq20069
  have eq20105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq20091
  have eq20106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq20090
  have eq20117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq20105
       have r₂ := eq76
       grind)
    | exact resolve eq20105 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq20105
  have eq20118 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20106
       have r₂ := eq27
       grind)
    | exact resolve eq20106 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20106
  have eq20121 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq20117
       have r₂ := eq27
       grind)
    | exact resolve eq20117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20117
  have eq20306 : y ≠ y ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20118
       grind)
    | exact superpose eq20118 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20118
       grind)
    | exact resolve eq13 eq20118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20307 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq20118
       grind)
    | exact superpose eq20118 eq14
    | exact resolve eq14 eq20118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20318 : (k x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20306
  have eq20330 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20121
       grind)
    | exact superpose eq20121 eq44
    | exact resolve eq44 eq20121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20121
  have eq20383 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq20330
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20330
    | exact resolve eq20330 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20330
  have eq20608 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20318
       grind)
    | exact superpose eq20318 eq44
    | exact resolve eq44 eq20318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20318
  have eq20816 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20307 x
       have i₂ := eq20118
       grind)
    | exact superpose eq20118 eq20307
    | exact resolve eq20307 eq20118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20118 eq20307
  have eq20887 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20816
  have eq20891 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20887
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20887
    | exact resolve eq20887 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20887
  have eq20894 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20608
       have i₂ := eq20891
       grind)
    | exact superpose eq20891 eq20608
    | exact resolve eq20608 eq20891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20608 eq20891
  have eq20911 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20894
  have eq20915 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20911
    | exact resolve eq20911 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20911
  have eq20928 : (τ (σ (M.op x y))) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20915 eq58
    | exact resolve eq58 eq20915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq20940 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20915 eq14649
    | exact resolve eq14649 eq20915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14649 eq20915
  have eq20954 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq20940
  have eq20965 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20954
       have r₂ := eq14641
       grind)
    | exact resolve eq20954 eq14641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14641 eq20954
  have eq20972 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq20928
    | exact resolve eq20928 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20928
  have eq20988 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20965 eq14
    | exact resolve eq14 eq20965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21033 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16527
       have i₂ := eq20972
       grind)
    | exact superpose eq20972 eq16527
    | exact resolve eq16527 eq20972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16527 eq20972
  have eq21047 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by grind
  clear eq21033
  have eq21109 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43
       have i₂ := eq21047
       grind)
    | exact superpose eq21047 eq43
    | exact resolve eq43 eq21047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq21047
  have eq21155 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4002 eq21109
    | exact resolve eq21109 eq4002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4002 eq21109
  have eq21168 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq21155
    | exact resolve eq21155 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21155
  have eq22085 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20965 eq20988
    | exact resolve eq20988 eq20965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20965 eq20988
  have eq22181 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq22085
  have eq22186 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq22181
    | exact resolve eq22181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22181
  have eq22209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22186 eq21168
    | exact resolve eq21168 eq22186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21168 eq22186
  have eq22221 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22209
  have eq22234 : y = (M.op x y) := by
    first
    | (have r₁ := eq22221
       have r₂ := eq27
       grind)
    | exact resolve eq22221 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22221
  have eq22236 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq22234 eq20
    | exact resolve eq20 eq22234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22285 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq22234 eq218
    | exact resolve eq218 eq22234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq22302 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22234 eq13694
    | exact resolve eq13694 eq22234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13694
  have eq22366 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq22236
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22236
    | exact resolve eq22236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22236
  have eq22403 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq22366 eq26
    | exact resolve eq26 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq22472 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq22366 eq6101
    | exact resolve eq6101 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6101
  have eq22499 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22366 eq16851
    | exact resolve eq16851 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16851
  have eq22500 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22366 eq17112
    | exact resolve eq17112 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17112
  have eq22502 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22366 eq20383
    | exact resolve eq20383 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20383
  have eq22509 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq22500
       have r₂ := eq27
       grind)
    | exact resolve eq22500 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22500
  have eq22510 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq22499
       have r₂ := eq27
       grind)
    | exact resolve eq22499 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22499
  have eq22514 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq22472
       have r₂ := eq27
       grind)
    | exact resolve eq22472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22472
  have eq23246 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq22510 eq14
    | exact resolve eq14 eq22510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28411 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22509 eq22502
    | exact resolve eq22502 eq22509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22502 eq22509
  have eq28419 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq28411
  have eq28788 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq22302
       grind)
    | exact superpose eq22302 eq16
    | exact resolve eq16 eq22302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22302
  have eq28873 : (M.op y y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4561 eq28788
    | exact resolve eq28788 eq4561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4561 eq28788
  have eq28882 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22234 eq28873
    | exact resolve eq28873 eq22234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28873
  have eq28891 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq28882
       have r₂ := eq13 y y
       grind)
    | exact resolve eq28882 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28882
  have eq28892 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq28891
       grind)
    | exact superpose eq28891 eq74
    | exact resolve eq74 eq28891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq28891
  have eq28927 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq4254 eq28892
    | exact resolve eq28892 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254 eq28892
  have eq28940 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22366 eq28927
    | exact resolve eq28927 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28927
  have eq36171 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22510 eq23246
    | exact resolve eq23246 eq22510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22510 eq23246
  have eq36240 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq36171
  have eq36252 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22403 eq36240
    | exact resolve eq36240 eq22403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36240
  have eq36285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq36252 eq28419
    | exact resolve eq28419 eq36252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28419 eq36252
  have eq36305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq36285
  have eq36320 : y = (M.op y x) := by
    first
    | (have r₁ := eq36305
       have r₂ := eq27
       grind)
    | exact resolve eq36305 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36305
  have eq36869 : y ≠ y ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq36320
       grind)
    | exact superpose eq36320 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq36320
       grind)
    | exact resolve eq13 eq36320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36871 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 y
       have i₂ := eq36320
       grind)
    | exact superpose eq36320 eq54
    | exact resolve eq54 eq36320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq36881 : (k x y) = (M.op x x) := by grind
  clear eq36869
  have eq36885 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq36871 X0 x
       have i₂ := eq22285 X0 x
       grind)
    | exact superpose eq22285 eq36871
    | exact resolve eq36871 eq22285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22285 eq36871
  have eq36907 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq36881
       grind)
    | exact superpose eq36881 eq44
    | exact resolve eq44 eq36881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq36881
  have eq36968 : (k (σ x) (σ (M.op x y))) = (σ (M.op x x)) := by
    first
    | exact superpose eq22366 eq36907
    | exact resolve eq36907 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36907
  have eq37049 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36885 x
       grind)
    | exact superpose eq36885 eq18
    | (have j1 := eq36885 x
       grind)
    | exact resolve eq18 eq36885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37058 : (σ (M.op y x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq28940
       have i₂ := eq36885 y
       grind)
    | exact superpose eq36885 eq28940
    | exact resolve eq28940 eq36885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28940 eq36885
  have eq37081 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq37058
       have i₂ := eq36320
       grind)
    | exact superpose eq36320 eq37058
    | exact resolve eq37058 eq36320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36320 eq37058
  have eq37088 : y = (M.op x x) := by
    first
    | exact superpose eq22234 eq37049
    | exact resolve eq37049 eq22234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22234 eq37049
  have eq37113 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq37081
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37081
    | exact resolve eq37081 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37081
  have eq37133 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22366 eq37113
    | exact resolve eq37113 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37113
  have eq37880 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq37133 eq14
    | exact resolve eq14 eq37133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37133
  have eq38015 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq36968
       have i₂ := eq37088
       grind)
    | exact superpose eq37088 eq36968
    | exact resolve eq36968 eq37088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36968 eq37088
  have eq38016 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq38015
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38015
    | exact resolve eq38015 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38015
  have eq38017 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq22366 eq38016
    | exact resolve eq38016 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22366 eq38016
  have eq38905 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq38017 eq22514
    | (have r₁ := eq22514
       have r₂ := eq38017
       grind)
    | exact resolve eq22514 eq38017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22514
  have eq38919 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq38905
  have eq38968 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq38919 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq38919
       grind)
    | exact resolve eq13 eq38919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38969 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq38919 eq14
    | exact resolve eq14 eq38919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38919
  have eq38980 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) := by grind
  clear eq38968
  have eq38983 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq38017 eq38980
    | exact resolve eq38980 eq38017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38017 eq38980
  have eq41526 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq37880 eq38969
    | exact resolve eq38969 eq37880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37880 eq38969
  have eq41613 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq41526 eq38983
    | exact resolve eq38983 eq41526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38983 eq41526
  have eq41630 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22403 eq41613
    | exact resolve eq41613 eq22403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22403 eq41613
  have eq41660 : False := by grind
  exact eq41660

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_x_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  clear eq24 eq35
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
  have eq56 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq58 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq78 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq14 X0 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 X0 X1 X2
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq78
    | (have j0 := eq78 X0 X1 X2
       grind)
    | exact resolve eq78 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
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
  have eq149 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq214 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq218 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq214 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq214
    | exact resolve eq214 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1379 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       have j1 := eq81 X0 X1
       grind)
    | (have r₁ := eq110 X0 X1
       have r₂ := eq81 X0 X1
       grind)
    | (have r₁ := eq110 X0 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq110 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq110
  have eq1555 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1379 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq1558 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1555 X0 X1
       have j1 := eq82 X1 X0 x
       grind)
    | (have r₁ := eq1555 X0 X1
       have r₂ := eq82 X0 X1 X0
       grind)
    | (have r₁ := eq1555 X1 X0
       have r₂ := eq82 X0 X1 X1
       grind)
    | exact resolve eq1555 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1555
  have eq1681 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1558 x y
       grind)
    | exact superpose eq1558 eq44
    | (have j1 := eq1558 x y
       grind)
    | exact resolve eq44 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1723 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1681
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1681
    | exact resolve eq1681 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681
  have eq1734 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq1723
    | exact resolve eq1723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq1744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1734 eq1558
    | (have j0 := eq1558 (σ x) (σ y)
       grind)
    | exact resolve eq1558 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq1744
    | exact resolve eq1744 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq1755 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1749
       have r₂ := eq27
       grind)
    | exact resolve eq1749 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749
  have eq1760 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1755 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1755
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1755
       grind)
    | exact resolve eq13 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq1767 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1760
  have eq1824 : (τ (σ x)) = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1767 eq55
    | exact resolve eq55 eq1767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1767
  have eq1830 : x = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq1824
    | exact resolve eq1824 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1824
  have eq1831 : x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq1830
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1830 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830
  have eq1835 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1831
       grind)
    | exact superpose eq1831 eq44
    | exact resolve eq44 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1841 : x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1558 x y
       have i₂ := eq1831
       grind)
    | exact superpose eq1831 eq1558
    | (have j0 := eq1558 y x
       grind)
    | exact resolve eq1558 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq1846 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1841
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1841
    | exact resolve eq1841 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq1852 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1835
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1835
    | exact resolve eq1835 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1861 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1852 eq1558
    | (have j0 := eq1558 (σ y) (σ x)
       grind)
    | exact resolve eq1558 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558 eq1852
  have eq1866 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1861
    | exact resolve eq1861 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq1884 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq1846
       grind)
    | exact superpose eq1846 eq14
    | exact resolve eq14 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1866 eq14
    | exact resolve eq14 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2125 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1884 x
       have i₂ := eq1846
       grind)
    | exact superpose eq1846 eq1884
    | exact resolve eq1884 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq1884
  have eq2164 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq2125
  have eq2167 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2164
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2164
    | exact resolve eq2164 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164
  have eq2177 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq2167
       grind)
    | exact superpose eq2167 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2167
       grind)
    | exact resolve eq12 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq2188 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) := by grind
  clear eq2177
  have eq2189 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq2188
  have eq2198 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2189
       grind)
    | exact superpose eq2189 eq43
    | exact resolve eq43 eq2189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2189
  have eq2215 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2198
    | exact resolve eq2198 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2962 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1866 eq1896
    | exact resolve eq1896 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866 eq1896
  have eq3007 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2962
  have eq3011 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3007
    | exact resolve eq3007 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007
  have eq3021 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3011 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3011
       grind)
    | exact resolve eq12 eq3011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3032 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq3021
  have eq3033 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3032
  have eq3103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3033 eq2215
    | exact resolve eq2215 eq3033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3113 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3103
       have r₂ := eq27
       grind)
    | exact resolve eq3103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3103
  have eq3116 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3113 eq218
    | exact resolve eq218 eq3113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq3119 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3113 eq27
    | exact resolve eq27 eq3113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4860 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq3116
    | (have j0 := eq3116 X0 (σ y)
       grind)
    | exact resolve eq3116 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq4930 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3113 eq4860
    | exact resolve eq4860 eq3113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4860
  have eq4969 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4930 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4930
  have eq4977 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4969
    | (have j0 := eq4969 (σ x)
       grind)
    | exact resolve eq4969 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4969
  have eq5035 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4977 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4977
       grind)
    | exact resolve eq13 eq4977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4977
  have eq5050 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5035
       have r₂ := eq3113
       grind)
    | exact resolve eq5035 eq3113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113 eq5035
  have eq5066 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5050 eq2215
    | exact resolve eq2215 eq5050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2215 eq5050
  have eq5077 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq5066
  have eq5091 : x = (M.op x y) := by
    first
    | (have r₁ := eq5077
       have r₂ := eq3119
       grind)
    | exact resolve eq5077 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119 eq5077
  have eq5098 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq5091 eq20
    | exact resolve eq20 eq5091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq5101 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq5091 eq56
    | exact resolve eq56 eq5091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq5179 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5098
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5098
    | exact resolve eq5098 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5098
  have eq5226 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5179 eq3033
    | exact resolve eq3033 eq5179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3033
  have eq5236 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq5226
       have r₂ := eq27
       grind)
    | exact resolve eq5226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5226
  have eq5303 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5236 eq149
    | exact resolve eq149 eq5236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq5236
  have eq5310 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5091 eq5303
    | exact resolve eq5303 eq5091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq6146 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq5101 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5101
    | (have j0 := eq5101 y
       grind)
    | exact resolve eq5101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101
  have eq6217 : (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq5091 eq6146
    | exact resolve eq6146 eq5091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6146
  have eq6253 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 y X0 y
       have i₂ := eq6217
       grind)
    | exact superpose eq6217 eq61
    | exact resolve eq61 eq6217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6217
  have eq6261 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq6253 X0 x
       have i₂ := eq61 x x X0 y
       grind)
    | exact superpose eq61 eq6253
    | exact resolve eq6253 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq6253
  have eq7016 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6261 x
       grind)
    | exact superpose eq6261 eq18
    | (have j1 := eq6261 x
       grind)
    | exact resolve eq18 eq6261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6261
  have eq7035 : x = (M.op x x) := by
    first
    | exact superpose eq5091 eq7016
    | exact resolve eq7016 eq5091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5091 eq7016
  have eq7071 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq7035
       grind)
    | exact superpose eq7035 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq7035
       grind)
    | exact resolve eq13 eq7035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7035
  have eq7082 : x = (k x x) := by grind
  clear eq7071
  have eq7091 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7082
       have i₂ := eq5310
       grind)
    | exact superpose eq5310 eq7082
    | exact resolve eq7082 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5310 eq7082
  have eq7279 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7091 eq15
    | exact resolve eq15 eq7091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7091
  have eq7325 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7279
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7279
    | exact resolve eq7279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7279
  have eq7335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5179 eq7325
    | exact resolve eq7325 eq5179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5179 eq7325
  have eq7342 : False := by grind
  exact eq7342

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  clear eq36
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq80 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq44
    | exact resolve eq44 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq81 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq77 sF2
       grind)
    | exact superpose eq77 eq50
    | exact resolve eq50 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq82 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq81
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq81
    | exact resolve eq81 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq83 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq77 sF2
       grind)
    | exact superpose eq77 eq80
    | exact resolve eq80 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq91 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq77 sF3
       grind)
    | exact superpose eq77 eq75
    | exact resolve eq75 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq92 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq91
    | exact resolve eq91 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq91
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq9970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq9970
    | exact resolve eq9970 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9970
  have eq9982 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq9971
       have r₂ := eq28
       grind)
    | exact resolve eq9971 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9971
  have eq10107 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq9982 eq55
    | exact resolve eq55 eq9982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10108 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq9982 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9982
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq9982
       grind)
    | exact resolve eq13 eq9982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10110 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq10108
  have eq10117 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq10110 eq59
    | exact resolve eq59 eq10110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq10118 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq10110 eq107
    | exact resolve eq107 eq10110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq10110
  have eq10130 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq10118
  have eq10140 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq82 eq10117
    | exact resolve eq10117 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10117
  have eq10141 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq10140
       have r₂ := eq13 x y
       grind)
    | exact resolve eq10140 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10140
  have eq10264 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq10141
       grind)
    | exact superpose eq10141 eq45
    | exact resolve eq45 eq10141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq10141
  have eq10287 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10264
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq10264
    | exact resolve eq10264 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10264
  have eq10327 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10287 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq10287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10287
  have eq10328 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq10327
  have eq10332 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq10328
    | exact resolve eq10328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10328
  have eq14163 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq9982 eq10107
    | exact resolve eq10107 eq9982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9982 eq10107
  have eq14197 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq14163 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14163
  have eq14339 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq14197
    | (have j0 := eq14197 (σ x)
       grind)
    | exact resolve eq14197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14197
  have eq14382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq14339 eq10130
    | exact resolve eq10130 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10130 eq14339
  have eq14395 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq14382
  have eq14400 : y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14395
       have r₂ := eq28
       grind)
    | exact resolve eq14395 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14395
  have eq14404 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 x X0 y
       have i₂ := eq14400
       grind)
    | exact superpose eq14400 eq55
    | exact resolve eq55 eq14400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14550 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14404 X0 x
       have i₂ := eq14400
       grind)
    | exact superpose eq14400 eq14404
    | exact resolve eq14404 eq14400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14404
  have eq14590 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq14550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14550
  have eq14593 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14590 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14590
    | (have j0 := eq14590 x
       grind)
    | exact resolve eq14590 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14610 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq14590 y
       grind)
    | exact superpose eq14590 eq92
    | exact resolve eq92 eq14590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq14590
  have eq14777 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq14593
       grind)
    | exact superpose eq14593 eq83
    | exact resolve eq83 eq14593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq14593
  have eq14807 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq14777
    | exact resolve eq14777 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14777
  have eq14825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14807 eq10332
    | exact resolve eq10332 eq14807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10332
  have eq14836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq14825
  have eq14842 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq14836
       have r₂ := eq28
       grind)
    | exact resolve eq14836 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14836
  have eq14995 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq14842 eq55
    | exact resolve eq55 eq14842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14842
  have eq15002 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14610
       have i₂ := eq14400
       grind)
    | exact superpose eq14400 eq14610
    | exact resolve eq14610 eq14400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14400 eq14610
  have eq15059 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15002
  have eq15065 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15059
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15059
    | exact resolve eq15059 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15059
  have eq15224 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq15065 eq55
    | exact resolve eq55 eq15065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq15065
  have eq17564 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14995 eq15224
    | exact resolve eq15224 eq14995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14995 eq15224
  have eq17593 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq17564 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17564
  have eq17754 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq17593
    | (have j0 := eq17593 (σ x)
       grind)
    | exact resolve eq17593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17593
  have eq17819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17754 eq14807
    | exact resolve eq14807 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14807 eq17754
  have eq17832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17819
  have eq17845 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17832
       have r₂ := eq28
       grind)
    | exact resolve eq17832 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17832
  have eq17848 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17845 eq30
    | exact resolve eq30 eq17845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17845
  have eq17963 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq17848
    | exact resolve eq17848 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17848
  have eq17964 : x = y := by grind
  clear eq17963
  have eq17979 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17964
       grind)
    | exact superpose eq17964 eq19
    | exact resolve eq19 eq17964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17980 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17964
       grind)
    | exact superpose eq17964 eq25
    | exact resolve eq25 eq17964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17964
  have eq18102 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17980
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17980
    | exact resolve eq17980 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17980
  have eq18121 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18102 eq27
    | exact resolve eq27 eq18102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18102
  have eq18320 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18121 eq82
    | exact resolve eq82 eq18121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq18121
  have eq18354 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18320
       have i₂ := eq17979
       grind)
    | exact superpose eq17979 eq18320
    | exact resolve eq18320 eq17979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17979 eq18320
  have eq18361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18354 eq15
    | exact resolve eq15 eq18354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18354
  have eq18437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18361
    | exact resolve eq18361 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18361
  have eq18458 : False := by grind
  exact eq18458

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq286 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq88 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq289 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq286 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq290 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq295 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq290
    | (have j0 := eq290 X0 X1
       grind)
    | exact resolve eq290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq304 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq295 X0 X1
       have j1 := eq288 X0 X1
       grind)
    | (have r₁ := eq295 X0 X1
       have r₂ := eq288 X0 X1
       grind)
    | (have r₁ := eq295 (k X0 X1) X0
       have r₂ := eq288 X0 X1
       grind)
    | (have r₁ := eq295 X0 X0
       have r₂ := eq288 X0 X0
       grind)
    | exact resolve eq295 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq295
  have eq579 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq304
    | exact resolve eq304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq304 x y
       grind)
    | exact superpose eq304 eq16
    | (have j1 := eq304 x y
       grind)
    | exact resolve eq16 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq603 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq579 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq579
    | (have j0 := eq579 X0 X1
       grind)
    | exact resolve eq579 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq579
  have eq609 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq603
    | exact resolve eq603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq708 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq609 (τ X0) X1
       grind)
    | exact superpose eq609 eq18
    | (have j1 := eq609 (τ X0) X1
       grind)
    | exact resolve eq18 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq609
  have eq904 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq708 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq708
    | exact resolve eq708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq959 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq904 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq904
    | (have j0 := eq904 X0 X1
       grind)
    | exact resolve eq904 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq1070 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq587
       have i₂ := eq959 x y
       grind)
    | exact superpose eq959 eq587
    | (have j1 := eq959 (σ x) (σ y)
       grind)
    | (have r₁ := eq587
       have r₂ := eq959 x y
       grind)
    | exact resolve eq587 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1070
  have eq1097 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1071
  have eq1110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq587
       have i₂ := eq1097
       grind)
    | exact superpose eq1097 eq587
    | exact resolve eq587 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq1097
  have eq1111 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1110
  have eq1112 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1111
  have eq1164 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1112
  have eq1178 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1164
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1164
    | exact resolve eq1164 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1184 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1178
       grind)
    | exact superpose eq1178 eq16
    | exact resolve eq16 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1202 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1184
       have i₂ := eq959 x y
       grind)
    | exact superpose eq959 eq1184
    | (have j1 := eq959 x y
       grind)
    | (have r₁ := eq1184
       have r₂ := eq959 x y
       grind)
    | exact resolve eq1184 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1203 : x = (M.op y y) := by grind
  clear eq1202
  have eq1210 : (M.op x y) = (k x y) := by grind
  clear eq1203
  have eq1265 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1184
       have i₂ := eq1210
       grind)
    | exact superpose eq1210 eq1184
    | exact resolve eq1184 eq1210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq1210
  have eq1268 : False := by grind
  exact eq1268

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq33 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X0) X3)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X3 X2 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq21 X0 X1 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X0) X3)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq70 X0 X1 X2 X3
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq70 X1 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq89 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 X0 X1 X2 x
       have i₂ := eq21 x X0 X1 X0
       grind)
    | exact superpose eq21 eq86
    | (have j0 := eq86 X0 X1 X2 x
       grind)
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq86
  have eq114 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq118 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       have j1 := eq89 X1 X1 X0
       grind)
    | (have r₁ := eq114 x X0
       have r₂ := eq89 X0 X0 x
       grind)
    | (have r₁ := eq114 X0 x
       have r₂ := eq89 X0 x x
       grind)
    | exact resolve eq114 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq114
  have eq238 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq118 (σ X1) (σ X0)
       grind)
    | exact superpose eq118 eq15
    | exact resolve eq15 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 X1
       have i₂ := eq118 X1 X0
       grind)
    | exact superpose eq118 eq238
    | exact resolve eq238 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq238
  have eq248 : False := by grind
  exact eq248
