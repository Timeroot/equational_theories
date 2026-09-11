import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
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
    | (have r₁ := eq22 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq40 X1 X0
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq40 X0 X1
       grind)
    | exact resolve eq45 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq45
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq51
  have eq165 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq169 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq165 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq165 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq165 X1 X1
       have r₂ := eq54 X1 X1
       grind)
    | exact resolve eq165 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq165
  have eq445 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq169 (σ X0) (σ X1)
       grind)
    | exact superpose eq169 eq15
    | exact resolve eq15 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X0 X1
       have i₂ := eq169 X0 X1
       grind)
    | exact superpose eq169 eq445
    | exact resolve eq445 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq445
  have eq452 : False := by grind
  exact eq452

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  clear eq44
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq87 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq73 sF3
       grind)
    | exact superpose eq73 eq71
    | exact resolve eq71 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq87
    | exact resolve eq87 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq87
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq54 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1549 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq486 X3 X1 x
       have i₂ := eq486 X0 X1 x
       grind)
    | (have i₁ := eq486 X0 X1 X3
       have i₂ := eq486 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq486 eq486
    | exact resolve eq486 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq13219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq13220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq13219
    | exact resolve eq13219 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13219
  have eq13230 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq13220
       have r₂ := eq28
       grind)
    | exact resolve eq13220 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13220
  have eq13233 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq13230 eq113
    | exact resolve eq113 eq13230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq13230
  have eq13340 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq13233
    | exact resolve eq13233 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13233
  have eq13341 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13340
  have eq13345 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq13341
       grind)
    | exact superpose eq13341 eq88
    | exact resolve eq88 eq13341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13405 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1549 X0 y x
       have i₂ := eq13341
       grind)
    | exact superpose eq13341 eq1549
    | exact resolve eq1549 eq13341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13341
  have eq13461 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13345
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13345
    | exact resolve eq13345 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13345
  have eq13822 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq13461 eq1549
    | exact resolve eq1549 eq13461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549 eq13461
  have eq14758 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13405 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13405
    | (have j0 := eq13405 x X0
       grind)
    | exact resolve eq13405 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13405
  have eq15140 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq14758 y
       grind)
    | exact superpose eq14758 eq88
    | exact resolve eq88 eq14758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq14758
  have eq15165 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq15140
    | exact resolve eq15140 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15140
  have eq39971 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq13822
    | (have j0 := eq13822 (σ x) X0
       grind)
    | exact resolve eq13822 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13822
  have eq40569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq39971 eq15165
    | exact resolve eq15165 eq39971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15165 eq39971
  have eq40580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq40569
  have eq40598 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq40580
       have r₂ := eq28
       grind)
    | exact resolve eq40580 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40580
  have eq40935 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq40598 eq30
    | exact resolve eq30 eq40598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq40598
  have eq41142 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq40935
    | exact resolve eq40935 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40935
  have eq41143 : x = y := by grind
  clear eq41142
  have eq41160 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq41143
       grind)
    | exact superpose eq41143 eq19
    | exact resolve eq19 eq41143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq41161 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq41143
       grind)
    | exact superpose eq41143 eq25
    | exact resolve eq25 eq41143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq41143
  have eq41282 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41161
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq41161
    | exact resolve eq41161 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq41161
  have eq41302 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq41282 eq27
    | exact resolve eq27 eq41282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq41282
  have eq42106 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq41302 eq78
    | exact resolve eq78 eq41302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq41302
  have eq42221 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq42106
       have i₂ := eq41160
       grind)
    | exact superpose eq41160 eq42106
    | exact resolve eq42106 eq41160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41160 eq42106
  have eq42225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42221 eq15
    | exact resolve eq15 eq42221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42221
  have eq42301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq42225
    | exact resolve eq42225 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq42225
  have eq42322 : False := by grind
  exact eq42322

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyx_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  clear eq47
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq16 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (k X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq178
    | exact resolve eq178 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq180 : ∀ X0 X1 X2 : G, (k X2 X2) = (M.op (M.op X1 X1) (M.op X0 (k X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 : G, (σ x) = (M.op (k X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq182 : ∀ X0 : G, x = (M.op (k X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq175
    | exact resolve eq175 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq183 : ∀ X0 X1 X2 : G, (k X2 X2) = (M.op (k X1 X1) (M.op X0 (k X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq180
    | exact resolve eq180 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op (M.op X1 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, x = (M.op (σ (k X0 X0)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq182 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq419 : ∀ X0 : G, x = (M.op (σ (σ (k X0 X0))) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq190 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq190
    | exact resolve eq190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq438 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq316
    | exact resolve eq316 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq637 : ∀ X0 X1 X3 : G, (M.op (k X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 : G, (M.op (k X1 X1) (k X0 X0)) = (M.op (σ x) (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq181 eq179
    | exact resolve eq179 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 : G, (M.op (k X1 X1) (k X0 X0)) = (M.op x (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq182 eq179
    | exact resolve eq179 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (k X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq179 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 x X0 y
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (k X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 (σ x) X0 (σ y)
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 X3 : G, (M.op (k X0 X0) X1) = (M.op (k X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 X1 X3 x
       have i₂ := eq179 X1 X0 x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 x X2
       have i₂ := eq179 X0 x X1
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (k X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 x
       have i₂ := eq179 X1 X0 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq181 x
       have i₂ := eq179 (M.op sF4 sF2) x x
       grind)
    | exact superpose eq179 eq181
    | exact resolve eq181 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq182 x
       have i₂ := eq179 (M.op sF0 x) x x
       grind)
    | exact superpose eq179 eq182
    | exact resolve eq182 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 X2 : G, (M.op (k X2 X2) (M.op (k X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq655 X0 X1 X2
       have i₂ := eq174 X2
       grind)
    | exact superpose eq174 eq655
    | exact resolve eq655 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq665 : ∀ X0 X1 X3 : G, (M.op (k X3 X3) (k X1 X1)) = (M.op X0 (k X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq637 X0 X0 X3
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq637
    | exact resolve eq637 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq667 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (τ (k X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq646 (τ X0)
       have i₂ := eq438 X0 X0
       grind)
    | exact superpose eq438 eq646
    | exact resolve eq646 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq179 x x X0
       have i₂ := eq646 x
       grind)
    | exact superpose eq646 eq179
    | exact resolve eq179 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq676 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq647 eq179
    | exact resolve eq179 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq795 : ∀ X0 X1 X2 : G, (M.op (τ (k X0 X0)) (M.op (M.op X1 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq184 (τ X0) X1 X2
       have i₂ := eq438 X0 X0
       grind)
    | exact superpose eq438 eq184
    | exact resolve eq184 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq822 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 (M.op (M.op X0 X1) X0) x X2
       have i₂ := eq184 x X0 X1
       grind)
    | exact superpose eq184 eq179
    | exact resolve eq179 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq870 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ x = y := by
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
  have eq875 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq919 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq994 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X1 X1)) = (k (k X1 X1) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (k X1 X1)
       have i₂ := eq649 X1 (k X1 X1) X0
       grind)
    | (have i₁ := eq174 (k X1 X1)
       have i₂ := eq649 X0 (k X1 X1) X1
       grind)
    | exact superpose eq649 eq174
    | exact resolve eq174 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq1003 : ∀ X1 : G, (M.op x (k X1 X1)) = (k (k X1 X1) (k X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq994 x X1
       have i₂ := eq644 X1 x
       grind)
    | exact superpose eq644 eq994
    | exact resolve eq994 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1064 : ∀ X0 X1 : G, (M.op x (k X0 X0)) = (M.op (M.op (k X0 X0) X1) (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq182 eq654
    | exact resolve eq654 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1065 : ∀ X0 X1 : G, (M.op (σ x) (k X0 X0)) = (M.op (M.op (k X0 X0) X1) (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq181 eq654
    | exact resolve eq654 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1101 : ∀ X0 : G, (M.op (σ x) (k X0 X0)) = (M.op x (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1064 X0 x
       have i₂ := eq1065 X0 x
       grind)
    | exact superpose eq1065 eq1064
    | exact resolve eq1064 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq1065
  have eq1115 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq658 sF4
       have i₂ := eq654 sF4 x sF2
       grind)
    | (have i₁ := eq658 sF4
       have i₂ := eq654 sF4 sF2 x
       grind)
    | exact superpose eq654 eq658
    | exact resolve eq658 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : ∀ X0 : G, x = (M.op (M.op (k X0 X0) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq659 sF0
       have i₂ := eq179 sF0 x x
       grind)
    | exact superpose eq179 eq659
    | exact resolve eq659 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1176 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k X1 X1) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 (k X0 X0) X1
       have i₂ := eq174 (k X0 X0)
       grind)
    | exact superpose eq174 eq663
    | exact resolve eq663 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq1194 : ∀ X0 : G, (k X0 X0) = (M.op x (k (k X0 X0) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1176 X0 x
       have i₂ := eq644 (k X0 X0) x
       grind)
    | exact superpose eq644 eq1176
    | exact resolve eq1176 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq1176
  have eq1195 : ∀ X0 : G, (k X0 X0) = (M.op (σ x) (k (k X0 X0) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1194 X0
       have i₂ := eq1101 (k X0 X0)
       grind)
    | exact superpose eq1101 eq1194
    | exact resolve eq1194 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1196 : ∀ X0 : G, (k X0 X0) = (M.op (σ x) (M.op x (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1195 X0
       have i₂ := eq1003 X0
       grind)
    | exact superpose eq1003 eq1195
    | exact resolve eq1195 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1197 : ∀ X0 : G, (k X0 X0) = (M.op (σ x) (M.op (σ x) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1196 X0
       have i₂ := eq1101 X0
       grind)
    | exact superpose eq1101 eq1196
    | exact resolve eq1196 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1262 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (σ x) (k X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq669 (k X0 X0)
       have i₂ := eq1101 X0
       grind)
    | exact superpose eq1101 eq669
    | exact resolve eq669 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq1298 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) X1) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq1115 eq654
    | exact resolve eq654 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1299 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1298 x x
       have i₂ := eq822 sF4 x x
       grind)
    | exact superpose eq822 eq1298
    | exact resolve eq1298 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq1298
  have eq1537 : ∀ X0 : G, x = (M.op (M.op (σ (k X0 X0)) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq1140 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1140
    | exact resolve eq1140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1750 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (M.op X1 (k X0 X0)) X2) (M.op X1 (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 (M.op X1 (k X0 X0)) x X2
       have i₂ := eq183 X1 x X0
       grind)
    | exact superpose eq183 eq179
    | exact resolve eq179 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq183
  have eq1766 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq870
       grind)
    | exact superpose eq870 eq40
    | exact resolve eq40 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq1767 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1766
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1766
    | exact resolve eq1766 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq1769 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq1767
    | exact resolve eq1767 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq4073 : ∀ X0 X1 X3 : G, (M.op X0 (k X1 X1)) = (M.op X3 (k X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq665 X3 X1 x
       have i₂ := eq665 X0 X1 x
       grind)
    | (have i₁ := eq665 X0 X1 X3
       have i₂ := eq665 (k X3 X3) X1 X3
       grind)
    | exact superpose eq665 eq665
    | exact resolve eq665 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4107 : ∀ X0 X1 : G, (M.op (σ x) (k X1 X1)) = (M.op X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq643 X1 x
       have i₂ := eq665 X0 X1 x
       grind)
    | (have i₁ := eq643 X1 X1
       have i₂ := eq665 (k X1 X1) X1 x
       grind)
    | exact superpose eq665 eq643
    | exact resolve eq643 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq4120 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (k (k X1 X1) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (k X1 X1)
       have i₂ := eq665 X0 X1 X1
       grind)
    | (have i₁ := eq174 (k X1 X1)
       have i₂ := eq665 (k X1 X1) X1 x
       grind)
    | exact superpose eq665 eq174
    | exact resolve eq174 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq4344 : ∀ X0 X1 : G, x = (M.op (M.op X0 (k X1 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq659 (k X1 X1)
       have i₂ := eq4073 (M.op sF0 x) X1 x
       grind)
    | (have i₁ := eq659 (k X1 X1)
       have i₂ := eq4073 X0 X1 (M.op sF0 x)
       grind)
    | exact superpose eq4073 eq659
    | exact resolve eq659 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4370 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (k X1 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq1262 X1
       have i₂ := eq4073 sF2 X1 x
       grind)
    | (have i₁ := eq1262 X1
       have i₂ := eq4073 X0 X1 sF2
       grind)
    | exact superpose eq4073 eq1262
    | exact resolve eq1262 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq4371 : ∀ X0 X1 : G, (k X1 X1) = (M.op (σ x) (M.op X0 (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1197 X1
       have i₂ := eq4073 sF2 X1 x
       grind)
    | (have i₁ := eq1197 X1
       have i₂ := eq4073 X0 X1 sF2
       grind)
    | exact superpose eq4073 eq1197
    | exact resolve eq1197 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq4372 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (k X1 X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq676 (k X1 X1)
       have i₂ := eq4073 sF2 X1 x
       grind)
    | (have i₁ := eq676 (k X1 X1)
       have i₂ := eq4073 X0 X1 sF2
       grind)
    | exact superpose eq4073 eq676
    | exact resolve eq676 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4373 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (k X1 X1)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1299 (k X1 X1)
       have i₂ := eq4073 sF4 X1 x
       grind)
    | (have i₁ := eq1299 (k X1 X1)
       have i₂ := eq4073 X0 X1 sF4
       grind)
    | exact superpose eq4073 eq1299
    | exact resolve eq1299 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq4601 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (k X1 X1)) X2) (M.op X0 (k X1 X1))) = (M.op x (M.op X0 (k X1 X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4344 eq654
    | exact resolve eq654 eq4344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4606 : ∀ X0 X1 : G, (k X1 X1) = (M.op x (M.op X0 (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4601 X0 X1 x
       have i₂ := eq1750 X1 X0 x
       grind)
    | exact superpose eq1750 eq4601
    | exact resolve eq4601 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750 eq4601
  have eq5303 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1769 eq875
    | exact resolve eq875 eq1769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq5311 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq5303
       have r₂ := eq27
       grind)
    | exact resolve eq5303 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq5352 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq5311 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq5311
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq5311
       grind)
    | exact resolve eq12 eq5311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5359 : ∀ X0 : G, (σ y) = (M.op (τ (k X0 X0)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5311 eq795
    | exact resolve eq795 eq5311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5360 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq5352
  have eq5361 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq5360
  have eq5364 : ∀ X0 : G, (σ y) = (M.op (τ (k X0 X0)) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq5359 X0
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq5359
    | exact resolve eq5359 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5359
  have eq5373 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq5364 x
       have i₂ := eq4120 (τ (k x x)) sF3
       grind)
    | exact superpose eq4120 eq5364
    | exact resolve eq5364 eq4120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5364
  have eq5377 : (σ y) = (M.op x (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq5373
       have i₂ := eq1003 sF3
       grind)
    | exact superpose eq1003 eq5373
    | exact resolve eq5373 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5373
  have eq5381 : (σ y) = (M.op (σ x) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq5377
       have i₂ := eq1101 sF3
       grind)
    | exact superpose eq1101 eq5377
    | exact resolve eq5377 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5377
  have eq5387 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq5361 eq1769
    | exact resolve eq1769 eq5361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1769 eq5361
  have eq5395 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5387
  have eq5414 : ∀ X0 : G, y = (M.op (τ (k X0 X0)) (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq795 X0 y x
       have i₂ := eq5395
       grind)
    | exact superpose eq5395 eq795
    | exact resolve eq795 eq5395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq5395
  have eq5419 : ∀ X0 : G, y = (M.op (τ (k X0 X0)) (k y y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5414 X0
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq5414
    | exact resolve eq5414 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414
  have eq5428 : y = (k (k y y) (k y y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5419 x
       have i₂ := eq4120 (τ (k x x)) y
       grind)
    | exact superpose eq4120 eq5419
    | exact resolve eq5419 eq4120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4120 eq5419
  have eq5432 : y = (M.op x (k y y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5428
       have i₂ := eq1003 y
       grind)
    | exact superpose eq1003 eq5428
    | exact resolve eq5428 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003 eq5428
  have eq5436 : y = (M.op (σ x) (k y y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5432
       have i₂ := eq1101 y
       grind)
    | exact superpose eq1101 eq5432
    | exact resolve eq5432 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101 eq5432
  have eq5544 : ∀ X0 : G, y = (M.op X0 (k y y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5436 eq4073
    | exact resolve eq4073 eq5436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5552 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5436 eq4606
    | exact resolve eq4606 eq5436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4606 eq5436
  have eq5571 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5552
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5552
    | exact resolve eq5552 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5552
  have eq5588 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq5571
       grind)
    | exact superpose eq5571 eq40
    | exact resolve eq40 eq5571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq5751 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5588
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5588
    | exact resolve eq5588 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5588
  have eq5775 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq5751
    | exact resolve eq5751 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5751
  have eq6884 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5544 X0
       have i₂ := eq5571
       grind)
    | exact superpose eq5571 eq5544
    | exact resolve eq5544 eq5571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5544 eq5571
  have eq6980 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq6884 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6884
  have eq7033 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6980 eq174
    | exact resolve eq174 eq6980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6980
  have eq7106 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7033 eq41
    | exact resolve eq41 eq7033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7033
  have eq7278 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq7106
    | exact resolve eq7106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7106
  have eq7320 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7278
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7278
    | exact resolve eq7278 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7278
  have eq8505 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq7320 eq4107
    | exact resolve eq4107 eq7320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4107 eq7320
  have eq8535 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq8505
    | (have j0 := eq8505 X0
       grind)
    | exact resolve eq8505 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8505
  have eq8709 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8535 eq174
    | exact resolve eq174 eq8535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8535
  have eq8769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5775 eq8709
    | exact resolve eq8709 eq5775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5775 eq8709
  have eq8778 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq8769
       have r₂ := eq27
       grind)
    | exact resolve eq8769 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8769
  have eq8781 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8778 eq31
    | exact resolve eq31 eq8778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8807 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq8781
    | exact resolve eq8781 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8781
  have eq8808 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq8807
  have eq8821 : (M.op x y) = (τ (σ y)) ∨ x = y := by
    first
    | exact superpose eq8808 eq28
    | exact resolve eq28 eq8808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq8808
  have eq8852 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq8821
    | exact resolve eq8821 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8821
  have eq8855 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq8852
       grind)
    | exact superpose eq8852 eq18
    | exact resolve eq18 eq8852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8870 : x ≠ (M.op x y) ∨ x = y := by grind
  have eq22182 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq5381 eq4371
    | exact resolve eq4371 eq5381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4371
  have eq22183 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq5381 eq4372
    | exact resolve eq4372 eq5381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22211 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq5311 eq22183
    | exact resolve eq22183 eq5311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5311 eq22183
  have eq22212 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq22182
    | exact resolve eq22182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22182
  have eq22241 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq8852 eq22211
    | exact resolve eq22211 eq8852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22211
  have eq22242 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq8852 eq22212
    | exact resolve eq22212 eq8852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22212
  have eq22263 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22241 eq658
    | exact resolve eq658 eq22241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq22305 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq22242 eq5381
    | exact resolve eq5381 eq22242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5381
  have eq22445 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq22305
  have eq22477 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq8852 eq22445
    | exact resolve eq22445 eq8852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22445
  have eq22478 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by grind
  clear eq22477
  have eq23680 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq22478 eq676
    | exact resolve eq676 eq22478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq22478
  have eq23698 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq22241 eq23680
    | exact resolve eq23680 eq22241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22241 eq23680
  have eq23719 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23698 eq654
    | exact resolve eq654 eq23698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23698
  have eq23730 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq23719 X0
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq23719
    | exact resolve eq23719 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23719
  have eq23738 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22242 eq23730
    | exact resolve eq23730 eq22242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22242 eq23730
  have eq23742 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq22263 eq23738
    | exact resolve eq23738 eq22263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22263 eq23738
  have eq23753 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23742 eq659
    | exact resolve eq659 eq23742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq23791 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23742 eq654
    | exact resolve eq654 eq23742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23814 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq23791 X0
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq23791
    | exact resolve eq23791 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23791
  have eq23826 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq23753 eq23814
    | exact resolve eq23814 eq23753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23753 eq23814
  have eq23861 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq23826 eq41
    | exact resolve eq41 eq23826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq23872 : x = (M.op (σ (σ x)) (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq23826 eq419
    | exact resolve eq419 eq23826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq23826
  have eq24042 : x = (M.op (σ (σ x)) (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq23872
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23872
    | exact resolve eq23872 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23872
  have eq24049 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq23861
    | exact resolve eq23861 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23861
  have eq24069 : x = (M.op (σ (σ x)) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq23742 eq24042
    | exact resolve eq24042 eq23742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24042
  have eq24072 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24049
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24049
    | exact resolve eq24049 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24049
  have eq24075 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq8778 eq24072
    | exact resolve eq24072 eq8778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8778 eq24072
  have eq24574 : x = (M.op (M.op (σ (σ x)) (M.op x y)) (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24075 eq1537
    | exact resolve eq1537 eq24075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq24075
  have eq24660 : x = (M.op (M.op (σ (σ x)) (M.op x y)) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq23742 eq24574
    | exact resolve eq24574 eq23742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23742 eq24574
  have eq24709 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24069 eq24660
    | exact resolve eq24660 eq24069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24069 eq24660
  have eq24727 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq8855 eq24709
    | exact resolve eq24709 eq8855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24709
  have eq24737 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq24727
       have r₂ := eq8870
       grind)
    | exact resolve eq24727 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24727
  have eq24749 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24737 eq919
    | (have r₁ := eq919
       have r₂ := eq24737
       grind)
    | exact resolve eq919 eq24737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq24766 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (k X1 X1)) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq24737 eq4373
    | exact resolve eq4373 eq24737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4373
  have eq24827 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq24749
  have eq24828 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24827
  have eq24834 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4372 eq24766
    | exact resolve eq24766 eq4372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4372 eq24766
  have eq24859 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24737 eq24834
    | exact resolve eq24834 eq24737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24834
  have eq24884 : (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24859
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq24859
    | exact resolve eq24859 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24859
  have eq24931 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24828 eq107
    | exact resolve eq107 eq24828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq24828
  have eq24936 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq24931
    | exact resolve eq24931 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24931
  have eq24939 : x = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8852 eq24936
    | exact resolve eq24936 eq8852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24936
  have eq24973 : ∀ X0 : G, (σ x) = (M.op X0 (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq24884 eq4073
    | exact resolve eq4073 eq24884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4073
  have eq24974 : x = (M.op (σ x) (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24884 eq4344
    | exact resolve eq4344 eq24884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4344
  have eq24977 : (M.op (M.op x y) x) = (M.op (σ x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24884 eq4370
    | exact resolve eq4370 eq24884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4370 eq24884
  have eq25096 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f25096_15 : ∀ X0 : G, (σ x) = (M.op X0 (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0
      grind
    have f25096_20 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
      intro X0 X1
      grind
    have f25096_23 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
      intro X0 X1 X2
      grind
    have f25096_24 : X0 ≠ (M.op (σ x) (M.op (M.op X0 X1) X0)) := by grind
    have f25096_25 : (σ x) ≠ (σ y) := by grind
    have f25096_26 : x ≠ y := by grind
    have f25096_28 : ∀ X0 : G, (σ x) = (M.op X0 (k (σ x) (σ x))) ∨ x = y := by
      intro X0
      first
      | (have j0 := f25096_15 X0
         grind)
      | (have r₁ := f25096_15 X0
         have r₂ := f25096_25
         grind)
      | exact resolve f25096_15 f25096_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25096_29 : ∀ X0 : G, (σ x) = (M.op X0 (k (σ x) (σ x))) := by
      intro X0
      first
      | (have j0 := f25096_28 X0
         grind)
      | (have r₁ := f25096_28 X0
         have r₂ := f25096_26
         grind)
      | exact resolve f25096_28 f25096_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25096_30 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
      intro X0
      grind
    have f25096_37 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f25096_23 X0 (M.op (σ x) (σ x)) X1
         have i₂ := f25096_30 (M.op (σ x) (σ x))
         grind)
      | exact superpose f25096_30 f25096_23
      | exact resolve f25096_23 f25096_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25096_80 : X0 ≠ X0 := by
      first
      | (have i₁ := f25096_24
         have i₂ := f25096_37 X0 X1
         grind)
      | exact superpose f25096_37 f25096_24
      | (have r₁ := f25096_24
         have r₂ := f25096_37 X0 X1
         grind)
      | exact resolve f25096_24 f25096_37
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25096_83 : False := by grind
    exact f25096_83
  have eq25107 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f25107_14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
      intro X0 X1 X2
      grind
    have f25107_15 : ∀ X0 : G, (σ x) = (M.op X0 (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0
      grind
    have f25107_20 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
      intro X0 X1
      grind
    have f25107_24 : (M.op (M.op X0 X1) X0) ≠ (M.op (σ x) X0) := by grind
    have f25107_25 : (σ x) ≠ (σ y) := by grind
    have f25107_26 : x ≠ y := by grind
    have f25107_28 : ∀ X0 : G, (σ x) = (M.op X0 (k (σ x) (σ x))) ∨ x = y := by
      intro X0
      first
      | (have j0 := f25107_15 X0
         grind)
      | (have r₁ := f25107_15 X0
         have r₂ := f25107_25
         grind)
      | exact resolve f25107_15 f25107_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25107_29 : ∀ X0 : G, (σ x) = (M.op X0 (k (σ x) (σ x))) := by
      intro X0
      first
      | (have j0 := f25107_28 X0
         grind)
      | (have r₁ := f25107_28 X0
         have r₂ := f25107_26
         grind)
      | exact resolve f25107_28 f25107_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25107_30 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
      intro X0
      grind
    have f25107_43 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X0) := by
      intro X0 X1
      first
      | (have i₁ := f25107_14 X0 (M.op (σ x) (σ x)) X1
         have i₂ := f25107_30 X0
         grind)
      | exact superpose f25107_30 f25107_14
      | exact resolve f25107_14 f25107_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25107_259 : (M.op (σ x) X0) ≠ (M.op (σ x) X0) := by
      first
      | (have i₁ := f25107_24
         have i₂ := f25107_43 X0 X1
         grind)
      | exact superpose f25107_43 f25107_24
      | (have r₁ := f25107_24
         have r₂ := f25107_43 X0 X1
         grind)
      | exact resolve f25107_24 f25107_43
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25107_274 : False := by grind
    exact f25107_274
  clear eq654
  have eq25248 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25107 eq25096
    | exact resolve eq25096 eq25107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25096 eq25107
  have eq25293 : x = (M.op (σ x) (k (M.op x y) x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24974
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq24974
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq24974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24974
  have eq25324 : x = (M.op (σ x) (k (M.op x y) x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x (M.op x y)) := by
    first
    | (have r₁ := eq25293
       have r₂ := eq8870
       grind)
    | exact resolve eq25293 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25293
  have eq25335 : x = (M.op (σ x) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq24939 eq25324
    | exact resolve eq25324 eq24939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24939 eq25324
  have eq25342 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq24977 eq25335
    | exact resolve eq25335 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24977 eq25335
  have eq25344 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8855 eq25342
    | exact resolve eq25342 eq8855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8855 eq25342
  have eq25345 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq25344
       have r₂ := eq8870
       grind)
    | exact resolve eq25344 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25344
  have eq25831 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq25248
    | (have j0 := eq25248 (σ y)
       grind)
    | exact resolve eq25248 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25248
  have eq25938 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24737 eq25831
    | exact resolve eq25831 eq24737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24737 eq25831
  have eq25954 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25938
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq25938
    | exact resolve eq25938 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25938
  have eq25978 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25954 eq24973
    | exact resolve eq24973 eq25954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24973
  have eq25981 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq25954 eq97
    | exact resolve eq97 eq25954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq25954
  have eq26121 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq25978 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25978
  have eq26205 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq25981
    | exact resolve eq25981 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25981
  have eq26260 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8852 eq26205
    | exact resolve eq26205 eq8852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8852 eq26205
  have eq26328 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26121 eq174
    | exact resolve eq174 eq26121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26121
  have eq27699 : (M.op (M.op x y) x) = (M.op (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26328 eq667
    | exact resolve eq667 eq26328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq26328
  have eq27872 : (M.op (M.op x y) x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq27699
    | exact resolve eq27699 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27699
  have eq27944 : (k x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27872
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq27872
    | exact resolve eq27872 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27872
  have eq27981 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq25345 eq27944
    | exact resolve eq27944 eq25345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25345 eq27944
  have eq27995 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26260 eq27981
    | exact resolve eq27981 eq26260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26260 eq27981
  have eq28000 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq27995
       have r₂ := eq8870
       grind)
    | exact resolve eq27995 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8870 eq27995
  have eq28006 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq28000 eq31
    | exact resolve eq31 eq28000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq28000
  have eq28038 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq28006
    | exact resolve eq28006 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28006
  have eq28039 : x = y := by grind
  clear eq28038
  have eq28057 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28039
       grind)
    | exact superpose eq28039 eq18
    | exact resolve eq18 eq28039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq28058 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq28039
       grind)
    | exact superpose eq28039 eq24
    | exact resolve eq24 eq28039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28039
  have eq28064 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28058
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28058
    | exact resolve eq28058 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28058
  have eq28065 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq28057
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq28057
    | exact resolve eq28057 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28057
  have eq28066 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28064 eq26
    | exact resolve eq26 eq28064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28064
  have eq28097 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28066
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq28066
    | exact resolve eq28066 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq28066
  have eq28099 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq28065
       grind)
    | exact superpose eq28065 eq39
    | exact resolve eq39 eq28065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq28065
  have eq28265 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28099
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28099
    | exact resolve eq28099 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28099
  have eq28281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28097 eq28265
    | exact resolve eq28265 eq28097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28097 eq28265
  have eq28284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq28281
    | exact resolve eq28281 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq28281
  have eq28286 : False := by grind
  exact eq28286

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  have eq53 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq118 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq121 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq118
  have eq122 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq121
  have eq211 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 : G, (σ x) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq377 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op (M.op X1 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (σ X0) X2
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq214 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq214
    | exact resolve eq214 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq494 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq56 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (σ X0) X2
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq56
    | exact resolve eq56 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq511 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 x X2
       have i₂ := eq56 X0 x X1
       grind)
    | (have i₁ := eq56 X2 X2 X2
       have i₂ := eq56 X2 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1151 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq513 sF0
       have i₂ := eq511 sF0 x x
       grind)
    | (have i₁ := eq513 sF0
       have i₂ := eq511 sF0 x x
       grind)
    | exact superpose eq511 eq513
    | exact resolve eq513 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq513
  have eq1490 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) = (M.op (σ (M.op X1 X1)) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1151 eq510
    | exact resolve eq510 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq1151
  have eq1493 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1490 x X0
       have i₂ := eq377 X0 sF0 x
       grind)
    | exact superpose eq377 eq1490
    | exact resolve eq1490 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq1490
  have eq1518 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq494 X3 X1 x
       have i₂ := eq494 X0 X1 x
       grind)
    | (have i₁ := eq494 X0 X1 X3
       have i₂ := eq494 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq494 eq494
    | exact resolve eq494 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1530 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq494 X0 (M.op X1 X1) X3
       have i₂ := eq494 X0 X1 X1
       grind)
    | (have i₁ := eq494 X0 (M.op X1 X1) X3
       have i₂ := eq494 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq494 eq494
    | exact resolve eq494 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1562 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X1)
       have i₂ := eq494 X0 X1 X1
       grind)
    | (have i₁ := eq53 (M.op X1 X1)
       have i₂ := eq494 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq494 eq53
    | exact resolve eq53 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1568 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq211 (M.op X1 X1)
       have i₂ := eq494 X0 X1 X1
       grind)
    | (have i₁ := eq211 (M.op X1 X1)
       have i₂ := eq494 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq494 eq211
    | exact resolve eq211 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq1570 : ∀ X0 X1 : G, (σ x) = (M.op (σ (M.op X0 (M.op X1 X1))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq375 (M.op X1 X1)
       have i₂ := eq494 X0 X1 X1
       grind)
    | (have i₁ := eq375 (M.op X1 X1)
       have i₂ := eq494 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq494 eq375
    | exact resolve eq375 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq1643 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1530 X0 X1 x X3
       have i₂ := eq55 X0 x X1
       grind)
    | exact superpose eq55 eq1530
    | exact resolve eq1530 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1530
  have eq2101 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1493 (M.op X1 X1)
       have i₂ := eq1518 sF0 X1 x
       grind)
    | (have i₁ := eq1493 (M.op X1 X1)
       have i₂ := eq1518 X0 X1 sF0
       grind)
    | exact superpose eq1518 eq1493
    | exact resolve eq1493 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq14393 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq76 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq14393
    | exact resolve eq14393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14393
  have eq14404 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq14394
       have r₂ := eq28
       grind)
    | exact resolve eq14394 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14394
  have eq14407 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14404 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14404
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14404
       grind)
    | exact resolve eq12 eq14404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14408 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14404 eq14
    | exact resolve eq14 eq14404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14404
  have eq14417 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq14407
  have eq14418 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq14417
  have eq14424 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14418 eq76
    | exact resolve eq76 eq14418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq14418
  have eq14435 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14424
  have eq14694 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq14435 eq1643
    | exact resolve eq1643 eq14435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq28547 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14435 eq14408
    | exact resolve eq14408 eq14435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14408 eq14435
  have eq28731 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq28547
  have eq28770 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28731 eq14694
    | exact resolve eq14694 eq28731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14694 eq28731
  have eq28879 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq28770 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28770
  have eq29290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28879 eq27
    | (have j1 := eq28879 (σ x)
       grind)
    | exact resolve eq27 eq28879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28879
  have eq29318 : y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq29290
       have r₂ := eq28
       grind)
    | exact resolve eq29290 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29290
  have eq29333 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq29318
       grind)
    | exact superpose eq29318 eq14
    | exact resolve eq14 eq29318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29470 : ∀ X0 : G, y = (M.op X0 (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq29333 x
       have i₂ := eq494 X0 y x
       grind)
    | (have i₁ := eq29333 X0
       have i₂ := eq494 (M.op X0 X0) y x
       grind)
    | exact superpose eq494 eq29333
    | exact resolve eq29333 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq29523 : x = (M.op y (M.op (M.op x y) x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1562 (M.op x x) y
       have i₂ := eq29333 x
       grind)
    | exact superpose eq29333 eq1562
    | exact resolve eq1562 eq29333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq29526 : (M.op (M.op x y) x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1568 (M.op x x) y
       have i₂ := eq29333 x
       grind)
    | exact superpose eq29333 eq1568
    | exact resolve eq1568 eq29333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29605 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1518 X0 (M.op y y) x
       have i₂ := eq29333 y
       grind)
    | exact superpose eq29333 eq1518
    | exact resolve eq1518 eq29333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29333
  have eq30022 : x = (M.op y (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29526 eq29523
    | exact resolve eq29523 eq29526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29523 eq29526
  have eq30038 : x = (M.op y (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq30022
  have eq30374 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq29605 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29605
    | (have j0 := eq29605 x X0
       grind)
    | exact resolve eq29605 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29605
  have eq30955 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq29470 X0
       have i₂ := eq30374 y
       grind)
    | exact superpose eq30374 eq29470
    | exact resolve eq29470 eq30374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29470
  have eq30963 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq30955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30955
  have eq31208 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30963 eq122
    | exact resolve eq122 eq30963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30963
  have eq31247 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq31208
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31208
    | exact resolve eq31208 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31208
  have eq32040 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30038
       have i₂ := eq29318
       grind)
    | exact superpose eq29318 eq30038
    | exact resolve eq30038 eq29318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29318 eq30038
  have eq32057 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq32040
  have eq32082 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30374 y
       have i₂ := eq32057
       grind)
    | exact superpose eq32057 eq30374
    | exact resolve eq30374 eq32057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30374 eq32057
  have eq32194 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq32082
  have eq32260 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq32194 eq30
    | exact resolve eq30 eq32194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32194
  have eq32370 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq32260
    | exact resolve eq32260 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32260
  have eq32371 : x = (M.op x y) ∨ x = y := by grind
  clear eq32370
  have eq32389 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq32371 eq21
    | exact resolve eq21 eq32371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32406 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq32371 eq122
    | exact resolve eq122 eq32371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq32467 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op X0 (M.op X1 X1)) x)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq32371 eq2101
    | exact resolve eq2101 eq32371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq32542 : x = (M.op x (M.op (M.op x y) x)) ∨ x = y := by
    first
    | (have i₁ := eq32467 x x
       have i₂ := eq1568 x x
       grind)
    | exact superpose eq1568 eq32467
    | exact resolve eq32467 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568 eq32467
  have eq32596 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq32406
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq32406
    | exact resolve eq32406 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq32406
  have eq32611 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq32389
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32389
    | exact resolve eq32389 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32389
  have eq32954 : x = (M.op x (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq32371 eq32542
    | exact resolve eq32542 eq32371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32371 eq32542
  have eq32975 : x = (M.op x (M.op x x)) ∨ x = y := by grind
  clear eq32954
  have eq34270 : ∀ X0 : G, x = (M.op X0 (M.op x x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq32975
       have i₂ := eq1518 x x X0
       grind)
    | (have i₁ := eq32975
       have i₂ := eq1518 X0 x x
       grind)
    | exact superpose eq1518 eq32975
    | exact resolve eq32975 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq34282 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq1570 x x
       have i₂ := eq32975
       grind)
    | exact superpose eq32975 eq1570
    | exact resolve eq1570 eq32975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570 eq32975
  have eq34320 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq34282
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34282
    | exact resolve eq34282 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34282
  have eq36621 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq383 (M.op x x)
       have i₂ := eq34270 (M.op x x)
       grind)
    | exact superpose eq34270 eq383
    | exact resolve eq383 eq34270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383 eq34270
  have eq36817 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq36621
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36621
    | exact resolve eq36621 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36621
  have eq40571 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq36817 eq34320
    | exact resolve eq34320 eq36817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34320 eq36817
  have eq40588 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y := by grind
  clear eq40571
  have eq42128 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq32596 eq40588
    | exact resolve eq40588 eq32596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32596 eq40588
  have eq42169 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by grind
  clear eq42128
  have eq43428 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31247 eq42169
    | exact resolve eq42169 eq31247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31247 eq42169
  have eq43481 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq43428
  have eq43487 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq43481
    | exact resolve eq43481 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43481
  have eq43489 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq43487 eq28
    | exact resolve eq28 eq43487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43487
  have eq43603 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq43489
       have r₂ := eq32611
       grind)
    | exact resolve eq43489 eq32611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32611 eq43489
  have eq43605 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq43603 eq30
    | exact resolve eq30 eq43603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq43603
  have eq43739 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq43605
    | exact resolve eq43605 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq43605
  have eq43740 : x = y := by grind
  clear eq43739
  have eq43757 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq43740
       grind)
    | exact superpose eq43740 eq19
    | exact resolve eq19 eq43740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq43758 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq43740
       grind)
    | exact superpose eq43740 eq25
    | exact resolve eq25 eq43740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq43740
  have eq43879 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq43758
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43758
    | exact resolve eq43758 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq43758
  have eq43898 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43879 eq27
    | exact resolve eq27 eq43879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq43879
  have eq44248 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq43898 eq68
    | exact resolve eq68 eq43898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq43898
  have eq44383 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq44248
       have i₂ := eq43757
       grind)
    | exact superpose eq43757 eq44248
    | exact resolve eq44248 eq43757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43757 eq44248
  have eq44397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44383 eq15
    | exact resolve eq15 eq44383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44383
  have eq44481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq44397
    | exact resolve eq44397 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq44397
  have eq44502 : False := by grind
  exact eq44502

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation1728 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  have eq67 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq71
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq71
    | exact resolve eq71 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq74
    | exact resolve eq74 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq632 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq68
    | (have j0 := eq68 X0 X1
       grind)
    | exact resolve eq68 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq68
  have eq714 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq632 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq9821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq76 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9821
    | exact resolve eq9821 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9821
  have eq9833 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq9822
       have r₂ := eq28
       grind)
    | exact resolve eq9822 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9822
  have eq9837 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9833
    | exact resolve eq9833 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9833
  have eq9846 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op (σ x) (σ y)) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9837 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9837
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9837
       grind)
    | exact resolve eq12 eq9837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9837
  have eq12962 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9846
    | (have j0 := eq9846 (σ x)
       grind)
    | (have r₁ := eq9846 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq9846 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9846
  have eq12963 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq12962
  have eq12964 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq12963
  have eq12972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq12964 eq76
    | exact resolve eq76 eq12964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq12964
  have eq12985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12972
  have eq12988 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12985
       have r₂ := eq28
       grind)
    | exact resolve eq12985 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12985
  have eq13114 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq12988
       grind)
    | exact superpose eq12988 eq96
    | exact resolve eq96 eq12988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13121 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq12988
       grind)
    | exact superpose eq12988 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12988
       grind)
    | exact resolve eq12 eq12988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12988
  have eq13155 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq13114
    | exact resolve eq13114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13114
  have eq18932 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13121 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13121
    | (have j0 := eq13121 x
       grind)
    | (have r₁ := eq13121 x
       have r₂ := eq19
       grind)
    | exact resolve eq13121 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13121
  have eq18933 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq18932
  have eq18934 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18933
  have eq19099 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq714 x y
       have i₂ := eq18934
       grind)
    | exact superpose eq18934 eq714
    | (have j0 := eq714 x y
       grind)
    | exact resolve eq714 eq18934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq18934
  have eq19103 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19099
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq19099
    | exact resolve eq19099 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19099
  have eq19115 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq19103
    | exact resolve eq19103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19103
  have eq19121 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19115
       have r₂ := eq13155
       grind)
    | exact resolve eq19115 eq13155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19115
  have eq19125 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19121
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq19121
    | exact resolve eq19121 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq19121
  have eq19129 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19125
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19125
    | exact resolve eq19125 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19125
  have eq19133 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19129
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19129
    | exact resolve eq19129 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19129
  have eq19137 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq19133
    | exact resolve eq19133 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19133
  have eq19141 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19137
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19137
    | exact resolve eq19137 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19137
  have eq19146 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19141
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19141
    | exact resolve eq19141 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19141
  have eq19147 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19146
  have eq19209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19147 eq13155
    | exact resolve eq13155 eq19147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13155 eq19147
  have eq19270 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19209
  have eq19276 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq19270
       have r₂ := eq28
       grind)
    | exact resolve eq19270 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19270
  have eq19431 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq19276 eq30
    | exact resolve eq30 eq19276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19276
  have eq19552 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq19431
    | exact resolve eq19431 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19431
  have eq19553 : x = y := by grind
  clear eq19552
  have eq19572 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq19553
       grind)
    | exact superpose eq19553 eq19
    | exact resolve eq19 eq19553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq19573 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq19553
       grind)
    | exact superpose eq19553 eq25
    | exact resolve eq25 eq19553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq19553
  have eq19687 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19573
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19573
    | exact resolve eq19573 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19573
  have eq19704 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19687 eq27
    | exact resolve eq27 eq19687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19687
  have eq19936 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19704 eq67
    | exact resolve eq67 eq19704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq19704
  have eq19973 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19936
       have i₂ := eq19572
       grind)
    | exact superpose eq19572 eq19936
    | exact resolve eq19936 eq19572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19572 eq19936
  have eq19986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19973 eq15
    | exact resolve eq15 eq19973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19973
  have eq20046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19986
    | exact resolve eq19986 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq19986
  have eq20060 : False := by grind
  exact eq20060

/-- `Equation177`: `x = (y ◇ y) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_x_pyx_Equation177 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law177 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law177.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq36
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
  clear eq38
  have eq44 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op y y)) := by
    first
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
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
  clear eq56
  have eq148 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq46
  have eq412 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq328
    | exact resolve eq328 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq556 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq148 (M.op X0 X0)
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq148
    | exact resolve eq148 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq148 (M.op X0 X0)
       grind)
    | exact superpose eq148 eq34
    | exact resolve eq34 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq560 : ∀ X0 : G, (M.op X0 (k X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq559 X0
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq559
    | exact resolve eq559 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq569 : (M.op x x) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq34 y (M.op x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq34
    | exact resolve eq34 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq574 : y = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq569 eq34
    | exact resolve eq34 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq582 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq45 eq34
    | exact resolve eq34 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq587 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq582 eq34
    | exact resolve eq34 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq647 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq650 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq710 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq1043 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq647
       grind)
    | exact superpose eq647 eq51
    | exact resolve eq51 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq1044 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1043
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1043
    | exact resolve eq1043 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1046 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1044
    | exact resolve eq1044 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0 (k X0 X0)
       have i₂ := eq710 X0 X0
       grind)
    | exact superpose eq710 eq34
    | (have j1 := eq710 X0 x
       grind)
    | exact resolve eq34 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq710
  have eq1108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1101 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1101 x
       have r₂ := eq13 (k x x) x
       grind)
    | (have r₁ := eq1101 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq1101 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq1101 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1182 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq556 X0
       have i₂ := eq1108 X0
       grind)
    | exact superpose eq1108 eq556
    | exact resolve eq556 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq1183 : ∀ X0 : G, (M.op X0 (k X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq560 X0
       have i₂ := eq1108 X0
       grind)
    | exact superpose eq1108 eq560
    | exact resolve eq560 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq1198 : y = (M.op (M.op x y) (k x x)) := by
    first
    | (have i₁ := eq574
       have i₂ := eq1108 x
       grind)
    | exact superpose eq1108 eq574
    | exact resolve eq574 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq1206 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq587
       have i₂ := eq1108 sF2
       grind)
    | exact superpose eq1108 eq587
    | exact resolve eq587 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq1433 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (k (σ X0) (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1183 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1183
    | exact resolve eq1183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1434 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (k (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1183 (τ X0)
       have i₂ := eq412 X0 X0
       grind)
    | exact superpose eq412 eq1183
    | exact resolve eq1183 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1446 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1434 X0
       have i₂ := eq412 (k X0 X0) X0
       grind)
    | exact superpose eq412 eq1434
    | exact resolve eq1434 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq1434
  have eq1447 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1433 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq1433
    | exact resolve eq1433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433
  have eq3910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1046 eq650
    | exact resolve eq650 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq1046
  have eq3921 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3910
       have r₂ := eq27
       grind)
    | exact resolve eq3910 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3910
  have eq3927 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3921
       have i₂ := eq1108 sF2
       grind)
    | exact superpose eq1108 eq3921
    | exact resolve eq3921 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq3930 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3927
       have i₂ := eq1108 x
       grind)
    | exact superpose eq1108 eq3927
    | exact resolve eq3927 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq3927
  have eq3935 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3930 eq109
    | exact resolve eq109 eq3930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq3930
  have eq3977 : y = (k x x) ∨ y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq3935
    | exact resolve eq3935 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3935
  have eq3978 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3977
  have eq3996 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq3978
       grind)
    | exact superpose eq3978 eq51
    | exact resolve eq51 eq3978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4004 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1182 x
       have i₂ := eq3978
       grind)
    | exact superpose eq3978 eq1182
    | exact resolve eq1182 eq3978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3978
  have eq4032 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4004
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4004
    | exact resolve eq4004 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004
  have eq4034 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3996
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3996
    | exact resolve eq3996 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3996
  have eq4044 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4034
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4034
    | exact resolve eq4034 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034
  have eq4131 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 x
       have i₂ := eq4032
       grind)
    | exact superpose eq4032 eq52
    | exact resolve eq52 eq4032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq4032
  have eq4137 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4131
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4131
    | exact resolve eq4131 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4131
  have eq4139 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4137
    | exact resolve eq4137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq4154 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4044 eq1182
    | exact resolve eq1182 eq4044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4044
  have eq4183 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4154
    | exact resolve eq4154 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4154
  have eq4196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4139 eq4183
    | exact resolve eq4183 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139 eq4183
  have eq4200 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4196
       have r₂ := eq27
       grind)
    | exact resolve eq4196 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196
  have eq4211 : (σ y) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4200 eq1206
    | exact resolve eq1206 eq4200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206 eq4200
  have eq4216 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4211
       have i₂ := eq1182 sF2
       grind)
    | exact superpose eq1182 eq4211
    | exact resolve eq4211 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4211
  have eq4270 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4216 eq1446
    | exact resolve eq1446 eq4216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446 eq4216
  have eq4279 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq4270
    | exact resolve eq4270 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4270
  have eq4283 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4279
    | exact resolve eq4279 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4279
  have eq4286 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4283
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4283
    | exact resolve eq4283 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4283
  have eq4287 : x = (M.op x y) := by grind
  clear eq4286
  have eq4289 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4287
       grind)
    | exact superpose eq4287 eq22
    | exact resolve eq22 eq4287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4299 : y = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1198
       have i₂ := eq4287
       grind)
    | exact superpose eq4287 eq1198
    | exact resolve eq1198 eq4287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq4287
  have eq4306 : y = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq4299
       have i₂ := eq1182 sF0
       grind)
    | exact superpose eq1182 eq4299
    | exact resolve eq4299 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182 eq4299
  have eq4322 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4289 eq20
    | exact resolve eq20 eq4289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4289
  have eq4449 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4306 eq1447
    | exact resolve eq1447 eq4306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447 eq4306
  have eq4456 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq4449
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4449
    | exact resolve eq4449 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4449
  have eq4460 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq4456
    | exact resolve eq4456 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4456
  have eq4463 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4322 eq4460
    | exact resolve eq4460 eq4322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4460
  have eq4958 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4463 eq26
    | exact resolve eq26 eq4463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4463
  have eq4978 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4958 eq27
    | exact resolve eq27 eq4958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4958
  have eq5001 : False := by grind
  exact eq5001

/-- `Equation177`: `x = (y ◇ y) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_x_pyx_Equation177 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law177 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law177.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X1 := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
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
  have eq37 : x = (M.op (M.op y y) (M.op x y)) := by
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
  have eq38 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq50 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq53 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq54 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq60 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq60
    | (have j0 := eq60 y
       grind)
    | exact resolve eq60 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq150 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X1 (M.op X0 X0)) X0
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq28
    | exact resolve eq28 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X0 X1) (M.op X1 X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq28
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (k X0 X1)) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq158 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq158 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq186 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq156
       grind)
    | exact superpose eq156 eq52
    | exact resolve eq52 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq187 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq186
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq186
    | exact resolve eq186 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq189 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq187
    | exact resolve eq187 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq189 eq157
    | exact resolve eq157 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq193
       have r₂ := eq27
       grind)
    | exact resolve eq193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq198 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq40
    | exact resolve eq40 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq199 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq39
    | exact resolve eq39 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq27
    | exact resolve eq27 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq352 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq15
    | exact resolve eq15 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1019 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq36
    | exact resolve eq36 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1039 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq198 eq36
    | exact resolve eq36 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq1072 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0))
       have i₂ := eq36 (M.op X1 X1) X0
       grind)
    | exact superpose eq36 eq35
    | exact resolve eq35 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (σ y)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1039
       have i₂ := eq1072 sF2 (M.op sF3 sF3)
       grind)
    | exact superpose eq1072 eq1039
    | exact resolve eq1039 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1114 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1019 X0 X1
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq1019
    | exact resolve eq1019 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1124 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1102
       have i₂ := eq1073 sF2 sF3
       grind)
    | exact superpose eq1073 eq1102
    | exact resolve eq1102 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1140 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1124 eq35
    | exact resolve eq35 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1151 : (σ y) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1140
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq1140
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq1140 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : (M.op (M.op (σ y) (σ y)) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1151 eq36
    | exact resolve eq36 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1221 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1151 eq16
    | exact resolve eq16 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1237 : (σ x) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq199 eq1218
    | exact resolve eq1218 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1316 : (σ x) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1237 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1319 : (σ x) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq175 x y
       grind)
    | (have r₁ := eq1316
       have r₂ := eq175 (σ x) (σ x)
       grind)
    | exact resolve eq1316 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1348 : (σ x) ≠ (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (M.op (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) (M.op (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ (σ y) = (k (σ y) (M.op (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1221 eq12
    | (have j0 := eq12 (σ y) (M.op (k (σ x) (σ x)) (k (σ x) (σ x)))
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1221
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq1221
       grind)
    | exact resolve eq12 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1354 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (M.op (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) (M.op (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ (σ y) = (k (σ y) (M.op (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq1348
       have r₂ := eq1237
       grind)
    | exact resolve eq1348 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1360 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ y) = (k (σ y) (M.op (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1354
       have i₂ := eq16 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq16 eq1354
    | exact resolve eq1354 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1362 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ y) = (k (σ y) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28 eq1360
    | (have j1 := eq28 (k (σ x) (σ x)) (k (σ x) (σ x))
       grind)
    | exact resolve eq1360 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1364 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1237 eq1362
    | exact resolve eq1362 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq1362
  have eq1366 : (σ y) = (k (σ y) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq175 x y
       grind)
    | (have r₁ := eq1364
       have r₂ := eq175 (σ x) (σ x)
       grind)
    | exact resolve eq1364 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq1367 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1319 eq1366
    | exact resolve eq1366 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319 eq1366
  have eq1368 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq189 eq1367
    | exact resolve eq1367 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1401 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1368 eq1140
    | exact resolve eq1140 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1406 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1368 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1368
       grind)
    | exact resolve eq13 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1411 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1406 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq1416 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1401
  have eq1449 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1368 eq1416
    | exact resolve eq1416 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368 eq1416
  have eq1507 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1449 eq32
    | exact resolve eq32 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq1621 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1507
    | exact resolve eq1507 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507
  have eq1630 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1621 eq29
    | exact resolve eq29 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621
  have eq1632 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq1630
    | exact resolve eq1630 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq1639 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq1632
       grind)
    | exact superpose eq1632 eq18
    | exact resolve eq18 eq1632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1960 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1411 eq26
    | (have j1 := eq1411 (σ y)
       grind)
    | exact resolve eq26 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq2077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq189 eq1960
    | exact resolve eq1960 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq2136 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2077
       have r₂ := eq27
       grind)
    | exact resolve eq2077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq2194 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2136 eq29
    | exact resolve eq29 eq2136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq2198 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2136 eq200
    | exact resolve eq200 eq2136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2199 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq2198
  have eq2203 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq2194
    | exact resolve eq2194 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq2249 : x = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1639 eq151
    | (have j0 := eq151 x (M.op x y)
       grind)
    | exact resolve eq151 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq1639
  have eq2281 : x = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2203 eq2249
    | exact resolve eq2249 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249
  have eq2282 : x = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2281
  have eq2347 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2203
       grind)
    | exact superpose eq2203 eq18
    | exact resolve eq18 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2349 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37
       have i₂ := eq2203
       grind)
    | exact superpose eq2203 eq37
    | exact resolve eq37 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203
  have eq2463 : x = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq2349
       have i₂ := eq28 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq28 eq2349
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq2349 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2471 : x = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq2282 eq2463
    | exact resolve eq2463 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282 eq2463
  have eq2473 : x = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2347 eq2471
    | exact resolve eq2471 eq2347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2347 eq2471
  have eq2474 : x = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2473
  have eq2477 : (σ x) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2474 eq50
    | exact resolve eq50 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2474
  have eq2480 : (σ x) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2477
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2477
    | exact resolve eq2477 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477
  have eq2481 : (σ x) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2136 eq2480
    | exact resolve eq2480 eq2136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq2580 : (σ x) = (k (σ y) (σ (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2481
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq2481
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq2481 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2582 : (σ x) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2481 eq175
    | (have j0 := eq175 (σ (M.op (M.op x y) (M.op x y))) (σ y)
       grind)
    | exact resolve eq175 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2585 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq54 eq2580
    | exact resolve eq2580 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2580
  have eq2587 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq2585
    | exact resolve eq2585 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2585
  have eq2588 : (σ x) = (k (σ y) (k (σ y) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2136 eq2587
    | exact resolve eq2587 eq2136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2136 eq2587
  have eq3281 : (M.op (M.op (σ y) (σ y)) (σ x)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2481 eq161
    | (have j0 := eq161 (σ y) (σ (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq161 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3320 : (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq199 eq3281
    | exact resolve eq3281 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq3281
  have eq3360 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3320
       have r₂ := eq2582
       grind)
    | exact resolve eq3320 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582 eq3320
  have eq3403 : (M.op (σ y) (σ y)) = (M.op (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3360 eq36
    | exact resolve eq36 eq3360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3404 : (σ (M.op (M.op x y) (M.op x y))) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3360 eq12
    | (have j0 := eq12 (σ y) (σ (M.op (M.op x y) (M.op x y)))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op (M.op x y) (M.op x y)))
       have r₂ := eq3360
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3360
       grind)
    | exact resolve eq12 eq3360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3405 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ y) (σ y)) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3360 eq16
    | exact resolve eq16 eq3360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360
  have eq3406 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq3404
  have eq3408 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2481 eq3406
    | exact resolve eq3406 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq3410 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3408
       have r₂ := eq2199
       grind)
    | exact resolve eq3408 eq2199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199 eq3408
  have eq3783 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3410 eq36
    | exact resolve eq36 eq3410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410
  have eq3790 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3403 eq3783
    | exact resolve eq3783 eq3403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403 eq3783
  have eq3797 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3790 eq3405
    | exact resolve eq3405 eq3790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3405
  have eq3799 : (σ x) = (k (σ y) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3790 eq2481
    | exact resolve eq2481 eq3790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481 eq3790
  have eq3806 : (σ x) = (k (σ y) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq3799
  have eq3808 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq3797
  have eq3813 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3808
       have i₂ := eq16 sF3 sF3
       grind)
    | exact superpose eq16 eq3808
    | exact resolve eq3808 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq3900 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3813 eq3806
    | exact resolve eq3806 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806 eq3813
  have eq3906 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3900
  have eq3941 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3906 eq2588
    | exact resolve eq2588 eq3906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2588 eq3906
  have eq3948 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq3941
  have eq3981 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq189 eq3948
    | exact resolve eq3948 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq3948
  have eq3983 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3981
       have r₂ := eq200
       grind)
    | exact resolve eq3981 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq3981
  have eq3989 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3983 eq2349
    | exact resolve eq2349 eq3983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349
  have eq4018 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3989
  have eq4028 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3983 eq4018
    | exact resolve eq4018 eq3983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3983 eq4018
  have eq4029 : x = (M.op x y) := by grind
  clear eq4028
  have eq4039 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4029
       grind)
    | exact superpose eq4029 eq22
    | exact resolve eq22 eq4029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4040 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq38
       have i₂ := eq4029
       grind)
    | exact superpose eq4029 eq38
    | exact resolve eq38 eq4029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq4042 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq4029
       grind)
    | exact superpose eq4029 eq52
    | exact resolve eq52 eq4029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq4043 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq352
       have i₂ := eq4029
       grind)
    | exact superpose eq4029 eq352
    | (have r₁ := eq352
       have r₂ := eq4029
       grind)
    | exact resolve eq352 eq4029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq4044 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq4043
  have eq4046 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4039 eq20
    | exact resolve eq20 eq4039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4039
  have eq4101 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
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
  have eq4126 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq4101 X0
       have i₂ := eq4029
       grind)
    | exact superpose eq4029 eq4101
    | exact resolve eq4101 eq4029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4101
  have eq4251 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op y y) (M.op y y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq4040 eq36
    | exact resolve eq36 eq4040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4040
  have eq4256 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op y y) (M.op x y)) (M.op (M.op y y) (M.op x y))) := by
    first
    | (have i₁ := eq4251
       have i₂ := eq1072 sF0 (M.op y y)
       grind)
    | exact superpose eq1072 eq4251
    | exact resolve eq4251 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072 eq4251
  have eq4260 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq4256
       have i₂ := eq1073 sF0 y
       grind)
    | exact superpose eq1073 eq4256
    | exact resolve eq4256 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073 eq4256
  have eq4371 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq4260 eq35
    | exact resolve eq35 eq4260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4260
  have eq4796 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq4044 eq4371
    | exact resolve eq4371 eq4044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4371
  have eq4799 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4044 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq4044
       grind)
    | exact resolve eq13 eq4044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4811 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq4799 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4799
  have eq4814 : y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4044 eq4796
    | exact resolve eq4796 eq4044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4796
  have eq5206 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq4811 eq4044
    | exact resolve eq4044 eq4811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4044 eq4811
  have eq5251 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq5206
  have eq5283 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5251 eq4042
    | exact resolve eq4042 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5296 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq20 eq5283
    | exact resolve eq5283 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5283
  have eq5300 : (σ x) = (k (σ x) (σ x)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq4046 eq5296
    | exact resolve eq5296 eq4046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5296
  have eq5354 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5300 eq184
    | (have j0 := eq184 (σ x) X0
       grind)
    | (have r₁ := eq184 (σ x) x
       have r₂ := eq5300
       grind)
    | exact resolve eq184 eq5300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq5300
  have eq5358 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq5354 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5354
  have eq5659 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5358 eq26
    | (have j1 := eq5358 (σ y)
       grind)
    | exact resolve eq26 eq5358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5358
  have eq5720 : (τ (M.op (σ x) (σ y))) = (k (τ (σ y)) (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5659 eq4126
    | exact resolve eq4126 eq5659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5659
  have eq5725 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq32 eq5720
    | exact resolve eq5720 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5720
  have eq5727 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq4814 eq5725
    | exact resolve eq5725 eq4814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4814 eq5725
  have eq5729 : y = (k y (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5251 eq5727
    | exact resolve eq5727 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5251 eq5727
  have eq5742 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5729 eq4042
    | exact resolve eq4042 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5729
  have eq5747 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5742
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5742
    | exact resolve eq5742 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5742
  have eq5757 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5747 eq157
    | exact resolve eq157 eq5747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq5747
  have eq5773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5757 eq14
    | exact resolve eq14 eq5757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5757
  have eq5776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5773
    | exact resolve eq5773 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5773
  have eq5779 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5776
       have r₂ := eq27
       grind)
    | exact resolve eq5776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5776
  have eq5783 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5779 eq39
    | exact resolve eq39 eq5779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq5788 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5779
  have eq5801 : (σ x) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq5783
       have i₂ := eq28 sF3 (M.op sF3 sF3)
       grind)
    | exact superpose eq28 eq5783
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq5783 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5807 : (σ x) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5783 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5812 : (σ x) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5807 eq5801
    | exact resolve eq5801 eq5807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5801 eq5807
  have eq5814 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5812
    | exact resolve eq5812 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5812
  have eq5815 : (σ x) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5814
  have eq5821 : (σ x) = (k (σ y) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5815
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq5815
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq5815 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5815
  have eq5976 : ∀ X0 X1 : G, (τ (k (k (σ X0) (σ x)) X1)) = (k (k X0 (M.op x y)) (τ X1)) := by
    intro X0 X1
    first
    | exact superpose eq4042 eq738
    | exact resolve eq738 eq4042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq4042
  have eq7040 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 (M.op (σ x) (σ x)))) (M.op x y)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4126 (M.op X0 (M.op sF2 sF2))
       have i₂ := eq150 X0 sF2
       grind)
    | exact superpose eq150 eq4126
    | (have j1 := eq150 (τ X0) (k (τ (M.op X0 (M.op (σ x) (σ x)))) (M.op x y))
       grind)
    | exact resolve eq4126 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4126
  have eq8500 : ∀ X0 X1 : G, (k (k (τ X0) (M.op x y)) (τ X1)) = (τ (k (k X0 (σ x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5976 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq5976
    | exact resolve eq5976 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5976
  have eq9449 : ∀ X0 : G, (τ (k (k X0 (σ x)) (k (σ y) (σ y)))) = (k (k (τ X0) (M.op x y)) (k y y)) := by
    intro X0
    first
    | exact superpose eq128 eq8500
    | exact resolve eq8500 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq8500
  have eq11012 : ∀ X0 X1 : G, (M.op (k X1 X1) (k X1 X1)) = (M.op (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1114 (M.op X1 X0) (k X0 X0)
       have i₂ := eq160 X0 X1
       grind)
    | exact superpose eq160 eq1114
    | (have j1 := eq160 X1 X1
       grind)
    | exact resolve eq1114 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11107 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X0 X1) X1
       have i₂ := eq1114 X1 X0
       grind)
    | exact superpose eq1114 eq35
    | exact resolve eq35 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1114
  have eq11157 : ∀ X1 : G, (M.op (k X1 X1) (k X1 X1)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq11012 x X1
       have i₂ := eq11107 x X1
       grind)
    | exact superpose eq11107 eq11012
    | (have j0 := eq11012 x X1
       grind)
    | exact resolve eq11012 eq11107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11012 eq11107
  have eq15107 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ y)))) = (k (k (τ (M.op X0 (M.op (σ x) (σ x)))) (M.op x y)) (k y y)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9449 (M.op X0 (M.op sF2 sF2))
       have i₂ := eq150 X0 sF2
       grind)
    | exact superpose eq150 eq9449
    | (have j1 := eq150 (τ (k X0 (k (σ y) (σ y)))) (k (k (τ (M.op X0 (M.op (σ x) (σ x)))) (M.op x y)) (k y y))
       grind)
    | exact resolve eq9449 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq9449
  have eq15188 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ y)))) = (k (τ X0) (k y y)) ∨ (σ x) = X0 := by
    intro X0
    first
    | exact superpose eq7040 eq15107
    | (have j0 := eq15107 X0
       have j1 := eq7040 X0
       grind)
    | exact resolve eq15107 eq7040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7040 eq15107
  have eq15308 : (τ (σ x)) = (k (τ (σ y)) (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5821 eq15188
    | (have j0 := eq15188 (σ y)
       grind)
    | exact resolve eq15188 eq5821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5821 eq15188
  have eq15353 : (τ (σ x)) = (k (τ (σ y)) (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq15308
       have r₂ := eq5788
       grind)
    | exact resolve eq15308 eq5788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15308
  have eq15366 : (τ (σ x)) = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq15353
    | exact resolve eq15353 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq15353
  have eq15369 : x = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq15366
    | exact resolve eq15366 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15366
  have eq15372 : (M.op x y) = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15369
       have i₂ := eq4029
       grind)
    | exact superpose eq4029 eq15369
    | exact resolve eq15369 eq4029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15369
  have eq15389 : (M.op (M.op y y) (M.op x y)) = (k y y) ∨ (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq161 y (k y y)
       have i₂ := eq15372
       grind)
    | exact superpose eq15372 eq161
    | (have j0 := eq161 y (k y y)
       grind)
    | exact resolve eq161 eq15372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq15390 : (M.op x y) ≠ (k y y) ∨ (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq175 (k y y) y
       have i₂ := eq15372
       grind)
    | exact superpose eq15372 eq175
    | (have j0 := eq175 (k y y) y
       grind)
    | exact resolve eq175 eq15372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15372
  have eq15391 : x = (k y y) ∨ (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq37 eq15389
    | exact resolve eq15389 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq15389
  have eq15393 : (M.op x y) = (k y y) ∨ (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15391
       have i₂ := eq4029
       grind)
    | exact superpose eq4029 eq15391
    | exact resolve eq15391 eq4029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4029 eq15391
  have eq15395 : (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq15393
       have r₂ := eq15390
       grind)
    | exact resolve eq15393 eq15390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15390 eq15393
  have eq18843 : (k y y) = (M.op (k y y) (k y y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq160 y (k y y)
       have i₂ := eq15395
       grind)
    | exact superpose eq15395 eq160
    | (have j0 := eq160 (k y y) x
       grind)
    | exact resolve eq160 eq15395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq15395
  have eq18846 : y = (k y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq11157 eq18843
    | (have j1 := eq11157 y
       grind)
    | exact resolve eq18843 eq11157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11157 eq18843
  have eq18849 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq175 (σ y) (σ y)
       grind)
    | (have r₁ := eq18846
       have r₂ := eq175 y y
       grind)
    | exact resolve eq18846 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18846
  have eq18897 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq18849 eq36
    | exact resolve eq36 eq18849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18849
  have eq18911 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5783 eq18897
    | exact resolve eq18897 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18897
  have eq18916 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18911
       have r₂ := eq5788
       grind)
    | exact resolve eq18911 eq5788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18911
  have eq18931 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq18916
       grind)
    | exact superpose eq18916 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq18916
       grind)
    | exact resolve eq13 eq18916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18952 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18931
  have eq19047 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18916
       have i₂ := eq18952 y
       grind)
    | exact superpose eq18952 eq18916
    | exact resolve eq18916 eq18952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18916 eq18952
  have eq19125 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19047
  have eq19200 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq19125
       grind)
    | exact superpose eq19125 eq53
    | exact resolve eq53 eq19125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq19125
  have eq19212 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19200
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19200
    | exact resolve eq19200 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19200
  have eq19302 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19212 eq175
    | (have j0 := eq175 (σ y) (σ y)
       grind)
    | (have r₁ := eq175 (σ y) (σ y)
       have r₂ := eq19212
       grind)
    | exact resolve eq175 eq19212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq19212
  have eq19303 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19302
  have eq19385 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19303 eq36
    | exact resolve eq36 eq19303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq19303
  have eq19399 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5783 eq19385
    | exact resolve eq19385 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5783 eq19385
  have eq19406 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19399
       have r₂ := eq5788
       grind)
    | exact resolve eq19399 eq5788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5788 eq19399
  have eq19410 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq19406 eq27
    | exact resolve eq27 eq19406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19406
  have eq19417 : False := by grind
  exact eq19417

/-- `Equation1833`: `x = (x ◇ (x ◇ x)) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation1833 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1833 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1833.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq44
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq44 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq113 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq114 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq116 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq116 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq122 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq43
    | exact resolve eq43 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq123 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq117 y
       grind)
    | exact superpose eq117 eq72
    | exact resolve eq72 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq125 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq84
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq84
    | exact resolve eq84 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq125
       have i₂ := eq117 y
       grind)
    | exact superpose eq117 eq125
    | exact resolve eq125 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq128 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq123
    | exact resolve eq123 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq129 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq122
    | exact resolve eq122 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq122
  have eq772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq106 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq772
    | exact resolve eq772 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq776 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq773
       have r₂ := eq27
       grind)
    | exact resolve eq773 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq778 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq776
    | exact resolve eq776 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq780 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq778 eq114
    | (have r₁ := eq114
       have r₂ := eq778
       grind)
    | exact resolve eq114 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq778
  have eq791 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq780
  have eq925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq791 eq106
    | exact resolve eq106 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq791
  have eq928 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq925
  have eq930 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq928
       have r₂ := eq27
       grind)
    | exact resolve eq928 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq968 : (τ (σ y)) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq930 eq126
    | exact resolve eq126 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq930
  have eq980 : (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq968
    | exact resolve eq968 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq968
  have eq982 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq980
       grind)
    | exact superpose eq980 eq113
    | (have r₁ := eq113
       have r₂ := eq980
       grind)
    | exact resolve eq113 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq984 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq129
       have i₂ := eq980
       grind)
    | exact superpose eq980 eq129
    | exact resolve eq129 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq980
  have eq996 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq982
  have eq997 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by grind
  clear eq996
  have eq999 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq984
    | exact resolve eq984 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1016 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq997
       grind)
    | exact superpose eq997 eq44
    | exact resolve eq44 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1018 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1016
    | exact resolve eq1016 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1018 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1018
  have eq1044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1043
    | exact resolve eq1043 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1047 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1044
       have r₂ := eq27
       grind)
    | exact resolve eq1044 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1049 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1047
    | exact resolve eq1047 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1049 eq999
    | exact resolve eq999 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq1049
  have eq1120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1102
  have eq1123 : y = (M.op y y) := by
    first
    | (have r₁ := eq1120
       have r₂ := eq27
       grind)
    | exact resolve eq1120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1125 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq128
       have i₂ := eq1123
       grind)
    | exact superpose eq1123 eq128
    | exact resolve eq128 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq1127 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1123
       grind)
    | exact superpose eq1123 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1123
       grind)
    | exact resolve eq13 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1136 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1144 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1125
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1125
    | exact resolve eq1125 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1125
  have eq1204 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1144 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1144
       grind)
    | exact resolve eq13 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1213 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1230 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1136 x
       grind)
    | exact superpose eq1136 eq44
    | exact resolve eq44 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1136
  have eq1241 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1230
    | exact resolve eq1230 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1230
  have eq1242 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1241
    | exact resolve eq1241 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1241
  have eq1454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1213 eq1242
    | exact resolve eq1242 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq1242
  have eq1470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1454
    | exact resolve eq1454 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1454
  have eq1479 : False := by grind
  exact eq1479
