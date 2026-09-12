import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyy_pxy_pyy_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 (k X1 X1) X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq45 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq46 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq57 X1 X0
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq57 X0 (M.op X1 X1)
       have r₂ := eq47 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq57 X1 X1
       have r₂ := eq47 (k X1 X1) X1
       grind)
    | exact resolve eq57 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq57
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq62 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq62
  have eq116 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq120 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       have j1 := eq66 X0 X1
       grind)
    | (have r₁ := eq116 X0 X1
       have r₂ := eq66 X0 X1
       grind)
    | (have r₁ := eq116 X0 X0
       have r₂ := eq66 X0 X0
       grind)
    | exact resolve eq116 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq116
  have eq312 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq120 (σ X0) (σ X1)
       grind)
    | exact superpose eq120 eq15
    | exact resolve eq15 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 X1
       have i₂ := eq120 X0 X1
       grind)
    | exact superpose eq120 eq312
    | exact resolve eq312 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq312
  have eq319 : False := by grind
  exact eq319

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyy_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq58 (τ X0)
       grind)
    | exact superpose eq58 eq18
    | exact resolve eq18 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq66
    | exact resolve eq66 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq66
  have eq83 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq368 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq409 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq368
  have eq413 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq409 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq409 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq409 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq416 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq413 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq413
    | (have j0 := eq413 X0 X1
       grind)
    | exact resolve eq413 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq975 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq416
    | exact resolve eq416 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq982 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq416 (σ X0) X1
       grind)
    | exact superpose eq416 eq15
    | (have j1 := eq416 (σ X0) X1
       grind)
    | exact resolve eq15 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq1003 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq982 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq982
    | (have j0 := eq982 X0 X1
       grind)
    | exact resolve eq982 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq982
  have eq1029 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq975 (τ X1) X0
       grind)
    | exact superpose eq975 eq17
    | (have j1 := eq975 (τ X1) X0
       grind)
    | exact resolve eq17 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq975
  have eq5105 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1029 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1029
    | exact resolve eq1029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq5161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5105 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5105
    | (have j0 := eq5105 X0 X1
       grind)
    | exact resolve eq5105 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5105
  have eq15375 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1003 x y
       grind)
    | exact superpose eq1003 eq16
    | (have j1 := eq1003 x y
       grind)
    | exact resolve eq16 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15527 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1003 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq15745 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq15375
       have i₂ := eq5161 y x
       grind)
    | exact superpose eq5161 eq15375
    | (have j1 := eq5161 y x
       grind)
    | (have r₁ := eq15375
       have r₂ := eq5161 y x
       grind)
    | exact resolve eq15375 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5161 eq15375
  have eq15746 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15745
  have eq15751 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15746
       grind)
    | exact superpose eq15746 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15746
       grind)
    | exact resolve eq13 eq15746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15770 : y = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15751
  have eq15910 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15527 (τ X1) (τ X0)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq15527
    | (have j0 := eq15527 (τ X1) (τ X0)
       grind)
    | exact resolve eq15527 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq15993 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15910 X0 X1
       have i₂ := eq72 X1
       grind)
    | exact superpose eq72 eq15910
    | (have j0 := eq15910 X0 X1
       grind)
    | exact resolve eq15910 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15910
  have eq16032 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15993 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq15993
    | (have j0 := eq15993 X0 X1
       grind)
    | exact resolve eq15993 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15993
  have eq16062 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16032 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16032
    | (have j0 := eq16032 X0 X1
       grind)
    | exact resolve eq16032 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16032
  have eq16088 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16062 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq16062
    | (have j0 := eq16062 X0 X1
       grind)
    | exact resolve eq16062 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16062
  have eq16107 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16088 X0 X1
       have i₂ := eq72 X1
       grind)
    | exact superpose eq72 eq16088
    | (have j0 := eq16088 X0 X1
       grind)
    | exact resolve eq16088 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq16088
  have eq61935 : y ≠ y ∨ (M.op x y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq15770
       grind)
    | exact superpose eq15770 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15770
       grind)
    | exact resolve eq12 eq15770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15770
  have eq61959 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq61935
  have eq251234 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61959
       grind)
    | exact superpose eq61959 eq16
    | exact resolve eq16 eq61959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61959
  have eq251310 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq251234
       have i₂ := eq15746
       grind)
    | exact superpose eq15746 eq251234
    | exact resolve eq251234 eq15746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15746 eq251234
  have eq251311 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq251310
  have eq251312 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq251311
  have eq251852 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq83 x (σ y)
       have i₂ := eq251312
       grind)
    | exact superpose eq251312 eq83
    | (have j0 := eq83 x (σ y)
       grind)
    | (have r₁ := eq83 x (σ y)
       have r₂ := eq251312
       grind)
    | exact resolve eq83 eq251312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq251919 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq251852
  have eq251923 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq251919
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq251919
    | exact resolve eq251919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251919
  have eq318192 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq251923
       grind)
    | exact superpose eq251923 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq251923
       grind)
    | exact resolve eq12 eq251923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251923
  have eq318247 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq318192
  have eq318271 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq318247
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq318247
    | exact resolve eq318247 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318247
  have eq1474887 : (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq251312
       have i₂ := eq318271
       grind)
    | exact superpose eq318271 eq251312
    | exact resolve eq251312 eq318271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251312 eq318271
  have eq1475127 : (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq1474887
  have eq1478938 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15527 x y
       have i₂ := eq1475127
       grind)
    | exact superpose eq1475127 eq15527
    | (have j0 := eq15527 x y
       grind)
    | (have r₁ := eq15527 x y
       have r₂ := eq1475127
       grind)
    | exact resolve eq15527 eq1475127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1478941 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16107 y x
       have i₂ := eq1475127
       grind)
    | exact superpose eq1475127 eq16107
    | (have j0 := eq16107 y x
       grind)
    | (have r₁ := eq16107 y x
       have r₂ := eq1475127
       grind)
    | exact resolve eq16107 eq1475127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475127
  have eq1479178 : (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq1478941
  have eq1479180 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq1478938
  have eq1479189 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq15527 x y
       grind)
    | (have r₁ := eq1479180
       have r₂ := eq15527 x y
       grind)
    | exact resolve eq1479180 eq15527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15527 eq1479180
  have eq1479205 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1479189
       grind)
    | exact superpose eq1479189 eq16
    | exact resolve eq16 eq1479189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479189
  have eq1492269 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1479205
       have i₂ := eq1479178
       grind)
    | exact superpose eq1479178 eq1479205
    | exact resolve eq1479205 eq1479178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479178
  have eq1492336 : (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq1492269
  have eq1492408 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1492336
       grind)
    | exact superpose eq1492336 eq10
    | exact resolve eq10 eq1492336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492336
  have eq1493033 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq1492408
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1492408
    | exact resolve eq1492408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492408
  have eq1497167 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16107 y x
       have i₂ := eq1493033
       grind)
    | exact superpose eq1493033 eq16107
    | (have j0 := eq16107 y x
       grind)
    | (have r₁ := eq16107 y x
       have r₂ := eq1493033
       grind)
    | exact resolve eq16107 eq1493033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16107 eq1493033
  have eq1497404 : (M.op x y) = (M.op x x) := by grind
  clear eq1497167
  have eq1497422 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1479205
       have i₂ := eq1497404
       grind)
    | exact superpose eq1497404 eq1479205
    | exact resolve eq1479205 eq1497404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479205 eq1497404
  have eq1497489 : False := by grind
  exact eq1497489

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_y_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq959 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq380 (τ X1) (τ X0)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq380
    | (have j0 := eq380 (τ X1) (τ X0)
       grind)
    | exact resolve eq380 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq959 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq959
    | (have j0 := eq959 X0 X1
       grind)
    | exact resolve eq959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq985 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq977 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq977
    | (have j0 := eq977 X0 X1
       grind)
    | exact resolve eq977 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq992 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq985
    | (have j0 := eq985 X0 X1
       grind)
    | exact resolve eq985 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq998 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq992 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq992
    | (have j0 := eq992 X0 X1
       grind)
    | exact resolve eq992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1003 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq998 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq998
    | (have j0 := eq998 X0 X1
       grind)
    | exact resolve eq998 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1006 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1003 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1003
    | (have j0 := eq1003 X0 X1
       grind)
    | exact resolve eq1003 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq4121 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq4133 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4121 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4121
  have eq4134 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133
  have eq4381 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88 y (σ x)
       grind)
    | exact superpose eq88 eq16
    | (have j1 := eq88 y (σ x)
       grind)
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq4389 : (σ (M.op x y)) ≠ (σ x) ∨ (τ (M.op (σ y) (σ x))) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4381
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4381
    | exact resolve eq4381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4381
  have eq98512 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4134 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4134
    | exact resolve eq4134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4134
  have eq98845 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq98512 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq98512
    | (have j0 := eq98512 X0 X1
       grind)
    | exact resolve eq98512 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98512
  have eq99148 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq98845 X1 X0
       grind)
    | exact superpose eq98845 eq11
    | (have j1 := eq98845 X1 X0
       grind)
    | exact resolve eq11 eq98845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98845
  have eq99357 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99148 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq99148
    | (have j0 := eq99148 X0 X1
       grind)
    | exact resolve eq99148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99148
  have eq99379 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq99357 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq99357 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq99357 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99357
  have eq100145 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq99379 X0 (σ X1)
       grind)
    | exact superpose eq99379 eq31
    | (have j1 := eq99379 X0 (σ X1)
       grind)
    | exact resolve eq31 eq99379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq100169 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq99379 X0 (τ X1)
       grind)
    | exact superpose eq99379 eq17
    | (have j1 := eq99379 X0 (τ X1)
       grind)
    | exact resolve eq17 eq99379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq100257 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq99379 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100924 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) X0
       have i₂ := eq100145 (σ X0) X1
       grind)
    | exact superpose eq100145 eq25
    | (have j1 := eq100145 (σ X0) X1
       grind)
    | exact resolve eq25 eq100145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100145
  have eq101047 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq100924 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq100924
    | (have j0 := eq100924 X0 X1
       grind)
    | exact resolve eq100924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100924
  have eq101135 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq101047 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101047
    | (have j0 := eq101047 X0 X1
       grind)
    | exact resolve eq101047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101047
  have eq101191 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq101135 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101135
    | (have j0 := eq101135 X0 X1
       grind)
    | exact resolve eq101135 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101135
  have eq101807 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq101191 (τ X0) (τ X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq101191
    | exact resolve eq101191 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq101191
  have eq102256 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101807 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq101807
    | (have j0 := eq101807 X0 X1
       grind)
    | exact resolve eq101807 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101807
  have eq102367 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq102256 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq102256
    | (have j0 := eq102256 X0 X1
       grind)
    | exact resolve eq102256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102256
  have eq104398 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq100169 (τ X0) X1
       grind)
    | exact superpose eq100169 eq18
    | (have j1 := eq100169 (τ X0) X1
       grind)
    | exact resolve eq18 eq100169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq100169
  have eq104494 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq104398 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq104398
    | (have j0 := eq104398 X0 X1
       grind)
    | exact resolve eq104398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104398
  have eq104613 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq104494 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq104494
    | (have j0 := eq104494 X0 X1
       grind)
    | exact resolve eq104494 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104494
  have eq104708 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104613 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq104613
    | (have j0 := eq104613 X0 X1
       grind)
    | exact resolve eq104613 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104613
  have eq105809 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq104708 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104708
    | (have j0 := eq104708 X1 (σ X0)
       grind)
    | exact resolve eq104708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104708
  have eq109385 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq102367 X1 X0
       grind)
    | exact superpose eq102367 eq11
    | (have j1 := eq102367 X1 X0
       grind)
    | exact resolve eq11 eq102367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109538 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq102367 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102367
  have eq109599 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq109385 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq109385
    | (have j0 := eq109385 X0 X1
       grind)
    | exact resolve eq109385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109385
  have eq110806 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq109599 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq109599
    | exact resolve eq109599 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109599
  have eq111102 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq110806 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq110806
    | (have j0 := eq110806 X0 X1
       grind)
    | exact resolve eq110806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110806
  have eq111124 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq111102 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq111102
    | (have j0 := eq111102 X0 X1
       grind)
    | exact resolve eq111102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111102
  have eq112406 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq111124 X1 X0
       have i₂ := eq99379 X0 X1
       grind)
    | exact superpose eq99379 eq111124
    | (have j0 := eq111124 X1 X0
       have j1 := eq99379 X0 X1
       grind)
    | exact resolve eq111124 eq99379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99379 eq111124
  have eq112930 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq112406 X0 X1
       have j1 := eq100257 X1 X0
       grind)
    | (have r₁ := eq112406 X1 X0
       have r₂ := eq100257 X0 X1
       grind)
    | exact resolve eq112406 eq100257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112406
  have eq114474 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105809 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq105809
    | exact resolve eq105809 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105809
  have eq114777 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq114474 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq114474
    | (have j0 := eq114474 X0 X1
       grind)
    | exact resolve eq114474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114474
  have eq117813 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq371
       have i₂ := eq114777 y x
       grind)
    | exact superpose eq114777 eq371
    | (have j1 := eq114777 y x
       grind)
    | (have r₁ := eq371
       have r₂ := eq114777 y x
       grind)
    | exact resolve eq371 eq114777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq117963 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq114777 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114777
  have eq117964 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq117813
  have eq118012 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq380 y x
       grind)
    | (have r₁ := eq117964
       have r₂ := eq380 x y
       grind)
    | exact resolve eq117964 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq117964
  have eq121749 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq100257 (σ x) (σ y)
       have i₂ := eq118012
       grind)
    | exact superpose eq118012 eq100257
    | (have j0 := eq100257 (σ x) (σ y)
       grind)
    | (have r₁ := eq100257 (σ x) (σ y)
       have r₂ := eq118012
       grind)
    | (have r₁ := eq100257 (σ y) (σ x)
       have r₂ := eq118012
       grind)
    | exact resolve eq100257 eq118012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100257 eq118012
  have eq121754 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq121749
  have eq121761 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq121754
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq121754
    | exact resolve eq121754 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121754
  have eq122487 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq121761
       grind)
    | exact superpose eq121761 eq16
    | exact resolve eq16 eq121761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122527 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq109538 (σ y) (σ x)
       have i₂ := eq121761
       grind)
    | exact superpose eq121761 eq109538
    | (have j0 := eq109538 (σ y) (σ x)
       grind)
    | exact resolve eq109538 eq121761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109538 eq121761
  have eq122530 : (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq122527
  have eq122535 : (τ (σ x)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq122530
       have i₂ := eq25 (σ y) x
       grind)
    | exact superpose eq25 eq122530
    | exact resolve eq122530 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq122530
  have eq122549 : (k y x) = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq122535
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq122535
    | exact resolve eq122535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122535
  have eq122554 : x = (k y x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq122549
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq122549
    | exact resolve eq122549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122549
  have eq123171 : x ≠ x ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1006 y x
       have i₂ := eq122554
       grind)
    | exact superpose eq122554 eq1006
    | (have j0 := eq1006 y x
       grind)
    | (have r₁ := eq1006 y x
       have r₂ := eq122554
       grind)
    | exact resolve eq1006 eq122554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122554
  have eq123183 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq123171
  have eq142239 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq117963 x y
       have i₂ := eq123183
       grind)
    | exact superpose eq123183 eq117963
    | (have j0 := eq117963 x y
       grind)
    | exact resolve eq117963 eq123183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117963 eq123183
  have eq142240 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq142239
  have eq142241 : x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq142240
  have eq142683 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq122487
       have i₂ := eq142241
       grind)
    | exact superpose eq142241 eq122487
    | exact resolve eq122487 eq142241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122487 eq142241
  have eq142729 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq142683
  have eq142730 : (σ y) = (σ (k x y)) := by grind
  clear eq142729
  have eq142758 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq142730
       grind)
    | exact superpose eq142730 eq10
    | exact resolve eq10 eq142730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142730
  have eq143003 : y = (k x y) := by
    first
    | (have i₁ := eq142758
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq142758
    | exact resolve eq142758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142758
  have eq143485 : y ≠ y ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1006 x y
       have i₂ := eq143003
       grind)
    | exact superpose eq143003 eq1006
    | (have j0 := eq1006 x y
       grind)
    | (have r₁ := eq1006 x y
       have r₂ := eq143003
       grind)
    | exact resolve eq1006 eq143003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq143497 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq143485
  have eq143503 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq143497
       grind)
    | exact superpose eq143497 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq143497
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq143497
       grind)
    | exact resolve eq12 eq143497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143497
  have eq143547 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq143503
  have eq147233 : x ≠ x ∨ (M.op y x) = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq143547
       grind)
    | exact superpose eq143547 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq143547
       grind)
    | exact resolve eq12 eq143547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143547
  have eq147276 : (M.op y x) = (k x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq147233
  have eq147289 : y = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq147276
       have i₂ := eq143003
       grind)
    | exact superpose eq143003 eq147276
    | exact resolve eq147276 eq143003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147276
  have eq147293 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq147289
       have r₂ := eq12 y x
       grind)
    | exact resolve eq147289 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147289
  have eq147800 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112930 x y
       have i₂ := eq147293
       grind)
    | exact superpose eq147293 eq112930
    | (have j0 := eq112930 x y
       grind)
    | exact resolve eq112930 eq147293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112930
  have eq147803 : x = (M.op x y) := by
    first
    | (have r₁ := eq147800
       have r₂ := eq16
       grind)
    | exact resolve eq147800 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147800
  have eq147812 : (σ x) ≠ (σ x) ∨ (τ (M.op (σ y) (σ x))) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4389
       have i₂ := eq147803
       grind)
    | exact superpose eq147803 eq4389
    | exact resolve eq4389 eq147803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4389 eq147803
  have eq147862 : (τ (M.op (σ y) (σ x))) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq147812
  have eq147875 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq147862
       have i₂ := eq143003
       grind)
    | exact superpose eq143003 eq147862
    | exact resolve eq147862 eq143003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143003 eq147862
  have eq172402 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq147875
       grind)
    | exact superpose eq147875 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq147875
       grind)
    | exact resolve eq12 eq147875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147875
  have eq172446 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (τ (M.op (σ y) (σ x))) := by grind
  clear eq172402
  have eq172460 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq172446
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq172446
    | exact resolve eq172446 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172446
  have eq172465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq172460
       have i₂ := eq147293
       grind)
    | exact superpose eq147293 eq172460
    | exact resolve eq172460 eq147293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172460
  have eq172469 : y = (τ (M.op (σ y) (σ x))) := by
    first
    | (have r₁ := eq172465
       have r₂ := eq16
       grind)
    | exact resolve eq172465 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172465
  have eq173193 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq11 (M.op (σ y) (σ x))
       have i₂ := eq172469
       grind)
    | exact superpose eq172469 eq11
    | exact resolve eq11 eq172469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172469
  have eq173401 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq173193
       grind)
    | exact superpose eq173193 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq173193
       grind)
    | exact resolve eq12 eq173193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173193
  have eq173445 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq173401
  have eq173459 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq173445
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq173445
    | exact resolve eq173445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173445
  have eq173464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq173459
       have i₂ := eq147293
       grind)
    | exact superpose eq147293 eq173459
    | exact resolve eq173459 eq147293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147293 eq173459
  have eq173468 : False := by grind
  exact eq173468

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pxy_pxx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq266 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq279 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq266 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq266
    | (have j0 := eq266 X0
       grind)
    | exact resolve eq266 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq266
  have eq282 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq279
    | (have j0 := eq279 X0
       grind)
    | exact resolve eq279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq282 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq282 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq282 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq293 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq283 (σ X0)
       grind)
    | exact superpose eq283 eq15
    | exact resolve eq15 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq293 X0
       have i₂ := eq283 X0
       grind)
    | exact superpose eq283 eq293
    | exact resolve eq293 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq293
  have eq358 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1479 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq362 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq362
    | (have j0 := eq362 (τ X0) (τ X1)
       grind)
    | exact resolve eq362 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1486 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1479 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1479
    | (have j0 := eq1479 X0 X1
       grind)
    | exact resolve eq1479 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1489 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1486 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1486
    | (have j0 := eq1486 X0 X1
       grind)
    | exact resolve eq1486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486
  have eq1491 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1489 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1489
    | (have j0 := eq1489 X0 X1
       grind)
    | exact resolve eq1489 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1492 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1491 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1491
    | (have j0 := eq1491 X0 X1
       grind)
    | exact resolve eq1491 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1493 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1492 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1492
    | (have j0 := eq1492 X0 X1
       grind)
    | exact resolve eq1492 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1494 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1493 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1493
    | (have j0 := eq1493 X0 X1
       grind)
    | exact resolve eq1493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq2118 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq358
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq358
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq358
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq358
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq358 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq2119 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2118
  have eq12684 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2119
       grind)
    | exact superpose eq2119 eq16
    | exact resolve eq16 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119
  have eq12685 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12684
       have r₂ := eq306 x
       grind)
    | exact resolve eq12684 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12684
  have eq12687 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq12685
       grind)
    | exact superpose eq12685 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq12685
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12685
       grind)
    | exact resolve eq12 eq12685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12685
  have eq12711 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12687
  have eq12718 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq362 x y
       have i₂ := eq12711
       grind)
    | exact superpose eq12711 eq362
    | (have j0 := eq362 x y
       grind)
    | exact resolve eq362 eq12711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq12711
  have eq12724 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12718
  have eq12725 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq12724
  have eq12923 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12725
       grind)
    | exact superpose eq12725 eq16
    | exact resolve eq16 eq12725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12925 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq12725
       grind)
    | exact superpose eq12725 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12725
       grind)
    | exact resolve eq12 eq12725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12725
  have eq12949 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq12925
  have eq12952 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq12949
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq12949
    | exact resolve eq12949 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12949
  have eq13147 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12952
       grind)
    | exact superpose eq12952 eq10
    | exact resolve eq10 eq12952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12952
  have eq13219 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq13147
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13147
    | exact resolve eq13147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13147
  have eq13235 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13219
       grind)
    | exact superpose eq13219 eq16
    | exact resolve eq16 eq13219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13219
  have eq13236 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq13235
       have r₂ := eq306 x
       grind)
    | exact resolve eq13235 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13235
  have eq13436 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq13236
       grind)
    | exact superpose eq13236 eq10
    | exact resolve eq10 eq13236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13236
  have eq13510 : x = (k x y) := by
    first
    | (have i₁ := eq13436
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13436
    | exact resolve eq13436 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13436
  have eq13531 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1494 x y
       have i₂ := eq13510
       grind)
    | exact superpose eq13510 eq1494
    | (have j0 := eq1494 x y
       grind)
    | (have r₁ := eq1494 x y
       have r₂ := eq13510
       grind)
    | exact resolve eq1494 eq13510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494 eq13510
  have eq13534 : x = y ∨ x = (M.op x y) := by grind
  clear eq13531
  have eq13661 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13534
       grind)
    | exact superpose eq13534 eq16
    | exact resolve eq16 eq13534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13534
  have eq13666 : x = (M.op x y) := by
    first
    | (have r₁ := eq13661
       have r₂ := eq306 x
       grind)
    | exact resolve eq13661 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13661
  have eq13670 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12923
       have i₂ := eq13666
       grind)
    | exact superpose eq13666 eq12923
    | exact resolve eq12923 eq13666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12923 eq13666
  have eq13697 : (σ x) = (σ y) := by grind
  clear eq13670
  have eq13818 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13697
       grind)
    | exact superpose eq13697 eq10
    | exact resolve eq10 eq13697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13697
  have eq13894 : x = y := by
    first
    | (have i₁ := eq13818
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13818
    | exact resolve eq13818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13818
  have eq13908 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13894
       grind)
    | exact superpose eq13894 eq16
    | exact resolve eq16 eq13894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13894
  have eq13914 : False := by grind
  exact eq13914

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pyx_pxx_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq85 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq207 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq195
    | (have j0 := eq195 X0
       grind)
    | exact resolve eq195 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq195
  have eq210 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq207 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq207
    | (have j0 := eq207 X0
       grind)
    | exact resolve eq207 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq211 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq210 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq210 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq210 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq218 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq211 (σ X0)
       grind)
    | exact superpose eq211 eq15
    | exact resolve eq15 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq218
    | exact resolve eq218 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq218
  have eq271 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1016 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1056 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1016 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1016
    | (have j0 := eq1016 X0 X1
       grind)
    | exact resolve eq1016 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq2088 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq271
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq271
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq271
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq271
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq271 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2089 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq2088
  have eq14360 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2089
       grind)
    | exact superpose eq2089 eq16
    | exact resolve eq16 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq14361 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq14360
       have r₂ := eq229 x
       grind)
    | exact resolve eq14360 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14360
  have eq14363 : y ≠ y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14361
       grind)
    | exact superpose eq14361 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14361
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14361
       grind)
    | exact resolve eq12 eq14361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14361
  have eq14382 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq14363
  have eq18212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq271
       have i₂ := eq14382
       grind)
    | exact superpose eq14382 eq271
    | exact resolve eq271 eq14382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq14382
  have eq18223 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq18212
  have eq18224 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq18223
  have eq18232 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq18224
       grind)
    | exact superpose eq18224 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18224
       grind)
    | exact resolve eq12 eq18224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18224
  have eq18251 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq18232
  have eq18259 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18251
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18251
    | exact resolve eq18251 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18251
  have eq18486 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18259
       grind)
    | exact superpose eq18259 eq16
    | exact resolve eq16 eq18259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18259
  have eq18519 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18486
       have i₂ := eq1056 x y
       grind)
    | exact superpose eq1056 eq18486
    | (have j1 := eq1056 x y
       grind)
    | (have r₁ := eq18486
       have r₂ := eq1056 x y
       grind)
    | (have r₁ := eq18486
       have r₂ := eq1056 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq18486
       have r₂ := eq1056 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq18486 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq18520 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq18519
  have eq18646 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18520
       grind)
    | exact superpose eq18520 eq16
    | exact resolve eq16 eq18520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18520
  have eq18647 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18646
       have r₂ := eq229 x
       grind)
    | exact resolve eq18646 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18646
  have eq18649 : y ≠ y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18647
       grind)
    | exact superpose eq18647 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18647
       grind)
    | exact resolve eq12 eq18647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18647
  have eq18668 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq18649
  have eq18811 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18486
       have i₂ := eq18668
       grind)
    | exact superpose eq18668 eq18486
    | exact resolve eq18486 eq18668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18486 eq18668
  have eq18825 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq18811
  have eq18826 : (σ x) = (σ y) := by grind
  clear eq18825
  have eq18827 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18826
       grind)
    | exact superpose eq18826 eq16
    | exact resolve eq16 eq18826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18828 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18826
       grind)
    | exact superpose eq18826 eq10
    | exact resolve eq10 eq18826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18826
  have eq18912 : x = y := by
    first
    | (have i₁ := eq18828
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18828
    | exact resolve eq18828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18828
  have eq18913 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18827
       have i₂ := eq229 x
       grind)
    | exact superpose eq229 eq18827
    | exact resolve eq18827 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq18827
  have eq18920 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18913
       have i₂ := eq18912
       grind)
    | exact superpose eq18912 eq18913
    | exact resolve eq18913 eq18912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18912 eq18913
  have eq18921 : False := by grind
  exact eq18921

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pxy_pyx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq108 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq108 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq108 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq140 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq131
    | exact resolve eq131 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq131
  have eq258 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140 x y
       grind)
    | exact superpose eq140 eq16
    | (have r₁ := eq16
       have r₂ := eq140 x y
       grind)
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq269 : False := by grind
  exact eq269

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_x_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq269 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq276 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq277 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq384 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq277 X1 X0
       grind)
    | exact superpose eq277 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq277 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq277 X0 X1
       grind)
    | exact resolve eq13 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq277 (σ x) (σ y)
       grind)
    | exact superpose eq277 eq16
    | (have j1 := eq277 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq384 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq395 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq390
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq390
    | exact resolve eq390 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq397 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq394 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq394 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq400 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq397 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq397
    | exact resolve eq397 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq397 X1 (τ X0)
       grind)
    | exact superpose eq397 eq18
    | (have j1 := eq397 X1 (τ X0)
       grind)
    | exact resolve eq18 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq428 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq397 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq411 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq411
    | exact resolve eq411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1628 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq411 X1 (τ X0)
       grind)
    | exact superpose eq411 eq17
    | (have j1 := eq411 X1 (τ X0)
       grind)
    | exact resolve eq17 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq411
  have eq1633 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1628 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1628
    | (have j0 := eq1628 X0 X1
       grind)
    | exact resolve eq1628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1645 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1604 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1604
    | (have j0 := eq1604 X0 X1
       grind)
    | exact resolve eq1604 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1646 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1633 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1633
    | (have j0 := eq1633 X0 X1
       grind)
    | exact resolve eq1633 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq1649 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1646 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1646
    | (have j0 := eq1646 X0 X1
       grind)
    | exact resolve eq1646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1708 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1649 X0 X1
       have i₂ := eq397 X0 X1
       grind)
    | exact superpose eq397 eq1649
    | (have j0 := eq1649 X1 X0
       have j1 := eq397 X1 X0
       grind)
    | exact resolve eq1649 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq1649
  have eq1768 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1708 X0 X1
       have j1 := eq428 X1 X0
       grind)
    | (have r₁ := eq1708 X1 X0
       have r₂ := eq428 X0 X1
       grind)
    | exact resolve eq1708 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq1708
  have eq1820 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq1768 X1 (σ X0)
       grind)
    | exact superpose eq1768 eq28
    | (have j1 := eq1768 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1768
  have eq1836 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1820 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1820
    | (have j0 := eq1820 X0 X1
       grind)
    | exact resolve eq1820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq1862 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1836 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1836
    | (have j0 := eq1836 X0 X1
       grind)
    | exact resolve eq1836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq2619 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1862 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1862
    | exact resolve eq1862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq4033 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq395
       have i₂ := eq277 x y
       grind)
    | exact superpose eq277 eq395
    | (have j1 := eq277 x y
       grind)
    | exact resolve eq395 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4036 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq4033
  have eq4320 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq400 y x
       have i₂ := eq4036
       grind)
    | exact superpose eq4036 eq400
    | (have j0 := eq400 y x
       grind)
    | exact resolve eq400 eq4036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq4036
  have eq4329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq4320
       have r₂ := eq395
       grind)
    | exact resolve eq4320 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq4320
  have eq4331 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq4329
       have r₂ := eq16
       grind)
    | exact resolve eq4329 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4329
  have eq4334 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4331
       grind)
    | exact superpose eq4331 eq16
    | exact resolve eq16 eq4331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4331
  have eq4381 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4334
       have i₂ := eq2619 x y
       grind)
    | exact superpose eq2619 eq4334
    | (have j1 := eq2619 x y
       grind)
    | exact resolve eq4334 eq2619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq4386 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq4334
       have i₂ := eq1645 x y
       grind)
    | exact superpose eq1645 eq4334
    | (have j1 := eq1645 x y
       grind)
    | (have r₁ := eq4334
       have r₂ := eq1645 x y
       grind)
    | exact resolve eq4334 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645 eq4334
  have eq4387 : y = (k y x) := by grind
  clear eq4386
  have eq4394 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq4381
       have r₂ := eq16
       grind)
    | exact resolve eq4381 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4381
  have eq4423 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq4394
       have i₂ := eq277 x y
       grind)
    | exact superpose eq277 eq4394
    | (have j1 := eq277 x y
       grind)
    | exact resolve eq4394 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq4426 : (M.op x y) = (k y x) := by grind
  clear eq4423
  have eq4427 : y = (M.op x y) := by
    first
    | (have i₁ := eq4426
       have i₂ := eq4387
       grind)
    | exact superpose eq4387 eq4426
    | exact resolve eq4426 eq4387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4387 eq4426
  have eq4428 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4394
       have i₂ := eq4427
       grind)
    | exact superpose eq4427 eq4394
    | exact resolve eq4394 eq4427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4394 eq4427
  have eq4452 : False := by grind
  exact eq4452

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyx_pxx_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq82 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = X0 := by
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
  have eq195 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq207 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq195
    | (have j0 := eq195 X0
       grind)
    | exact resolve eq195 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq195
  have eq210 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq207 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq207
    | (have j0 := eq207 X0
       grind)
    | exact resolve eq207 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq211 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq210 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq210 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq210 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq218 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq211 (σ X0)
       grind)
    | exact superpose eq211 eq15
    | exact resolve eq15 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq218
    | exact resolve eq218 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq218
  have eq271 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1022 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1059 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1022 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1022
    | (have j0 := eq1022 X0 X1
       grind)
    | exact resolve eq1022 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq2100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq271
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq271
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq271
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq271
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq271 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2101 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq2100
  have eq14376 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2101
       grind)
    | exact superpose eq2101 eq16
    | exact resolve eq16 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq14377 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq14376
       have r₂ := eq229 x
       grind)
    | exact resolve eq14376 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14376
  have eq14379 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14377
       grind)
    | exact superpose eq14377 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14377
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14377
       grind)
    | exact resolve eq12 eq14377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14377
  have eq14397 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq14379
  have eq17929 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq271
       have i₂ := eq14397
       grind)
    | exact superpose eq14397 eq271
    | exact resolve eq271 eq14397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq14397
  have eq17938 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq17929
  have eq17939 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq17938
  have eq17947 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq17939
       grind)
    | exact superpose eq17939 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17939
       grind)
    | exact resolve eq12 eq17939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17939
  have eq17965 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq17947
  have eq17973 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17965
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17965
    | exact resolve eq17965 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17965
  have eq18193 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17973
       grind)
    | exact superpose eq17973 eq16
    | exact resolve eq16 eq17973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17973
  have eq18225 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18193
       have i₂ := eq1059 y x
       grind)
    | exact superpose eq1059 eq18193
    | (have j1 := eq1059 (σ x) (σ y)
       grind)
    | (have r₁ := eq18193
       have r₂ := eq1059 y x
       grind)
    | (have r₁ := eq18193
       have r₂ := eq1059 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq18193
       have r₂ := eq1059 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq18193 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq18226 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq18225
  have eq18446 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18226
       grind)
    | exact superpose eq18226 eq16
    | exact resolve eq16 eq18226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18226
  have eq18447 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18446
       have r₂ := eq229 x
       grind)
    | exact resolve eq18446 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18446
  have eq18449 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18447
       grind)
    | exact superpose eq18447 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18447
       grind)
    | exact resolve eq12 eq18447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18447
  have eq18467 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq18449
  have eq18657 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18193
       have i₂ := eq18467
       grind)
    | exact superpose eq18467 eq18193
    | exact resolve eq18193 eq18467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18193 eq18467
  have eq18669 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq18657
  have eq18670 : (σ x) = (σ y) := by grind
  clear eq18669
  have eq18671 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18670
       grind)
    | exact superpose eq18670 eq16
    | exact resolve eq16 eq18670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18672 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18670
       grind)
    | exact superpose eq18670 eq10
    | exact resolve eq10 eq18670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18670
  have eq18756 : x = y := by
    first
    | (have i₁ := eq18672
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18672
    | exact resolve eq18672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18672
  have eq18757 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18671
       have i₂ := eq229 x
       grind)
    | exact superpose eq229 eq18671
    | exact resolve eq18671 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq18671
  have eq18764 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18757
       have i₂ := eq18756
       grind)
    | exact superpose eq18756 eq18757
    | exact resolve eq18757 eq18756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18756 eq18757
  have eq18765 : False := by grind
  exact eq18765
