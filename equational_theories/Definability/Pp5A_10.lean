import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pxy_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq79
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq14 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq379 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X2 ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq52 X0 X1 X2
       grind)
    | (have i₁ := eq12 X0 (M.op X2 X2)
       have i₂ := eq52 X2 X1 X2
       grind)
    | exact superpose eq52 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) (M.op X2 X2))
       have r₂ := eq52 X0 (M.op (M.op X0 X0) (M.op X2 X2)) X2
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq52 X1 X1 X1
       grind)
    | exact resolve eq12 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq495 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X1 X1
       have i₂ := eq379 X0 (σ X1)
       grind)
    | (have i₁ := eq73 X1 X1
       have i₂ := eq379 (σ X1) X1
       grind)
    | exact superpose eq379 eq73
    | exact resolve eq73 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq522 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq495 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq555 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq265 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq265
    | (have j0 := eq265 X0 y
       grind)
    | exact resolve eq265 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       grind)
    | (have r₁ := eq108 x X1
       have r₂ := eq52 x x x
       grind)
    | (have r₁ := eq108 (M.op x x) X1
       have r₂ := eq52 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq108 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq108
  have eq744 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) (M.op X1 X1)))) = (σ (M.op (τ X0) (M.op (M.op X1 X1) (M.op X1 X1)))) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq718 X1 (τ X0)
       grind)
    | exact superpose eq718 eq35
    | (have j1 := eq718 X1 (τ X0)
       grind)
    | exact resolve eq35 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq5733 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op X0 x)) ∨ (M.op X0 X0) = X0 ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq29 eq262
    | (have j0 := eq262 X0 x
       grind)
    | exact resolve eq262 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq5783 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 x)) ∨ (M.op X0 X0) = X0 ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq36 eq5733
    | (have j0 := eq5733 X0
       grind)
    | exact resolve eq5733 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5733
  have eq7214 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq382 X0 X1 (M.op (M.op X0 X0) (M.op X1 X1)) X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq7297 : ∀ X0 : G, (k (σ x) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) = (σ (M.op x (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq29 eq744
    | exact resolve eq744 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq7372 : ∀ X0 : G, (σ (M.op x (M.op (M.op X0 X0) (M.op X0 X0)))) = (σ (k x (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq36 eq7297
    | (have j0 := eq7297 X0
       grind)
    | exact resolve eq7297 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq7297
  have eq12870 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq522 X0 (τ X1)
       grind)
    | exact superpose eq522 eq35
    | (have j1 := eq522 X0 (τ X1)
       grind)
    | exact resolve eq35 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12872 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (σ y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq71
       have i₂ := eq522 X0 y
       grind)
    | exact superpose eq522 eq71
    | (have j1 := eq522 X0 y
       grind)
    | exact resolve eq71 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq12955 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (σ y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12872 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12872
    | (have j0 := eq12872 X0
       grind)
    | exact resolve eq12872 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12872
  have eq12957 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12870 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12870
    | (have j0 := eq12870 X0 X1
       grind)
    | exact resolve eq12870 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12870
  have eq12979 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12957 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12957
    | (have j0 := eq12957 X0 X1
       grind)
    | exact resolve eq12957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12957
  have eq13166 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ y) (σ y)) ∨ (σ y) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq379 X1 X0
       have i₂ := eq12955 X0
       grind)
    | exact superpose eq12955 eq379
    | (have j1 := eq12955 X1
       grind)
    | exact resolve eq379 eq12955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12955
  have eq13656 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12979 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19447 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq19448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19447
    | exact resolve eq19447 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19447
  have eq19459 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19448
       have r₂ := eq28
       grind)
    | exact resolve eq19448 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19448
  have eq19478 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq19459 eq379
    | exact resolve eq379 eq19459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19490 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq19459 eq409
    | exact resolve eq409 eq19459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19459
  have eq21848 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19490 eq100
    | exact resolve eq100 eq19490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19490
  have eq24671 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21848
       have i₂ := eq19478 sF3
       grind)
    | exact superpose eq19478 eq21848
    | exact resolve eq21848 eq19478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19478 eq21848
  have eq24747 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq24671
  have eq24779 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq24747
    | exact resolve eq24747 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24747
  have eq24783 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13656 (σ x) (σ x)
       grind)
    | (have r₁ := eq24779
       have r₂ := eq13656 x y
       grind)
    | exact resolve eq24779 eq13656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24779
  have eq25031 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq24783
       have i₂ := eq379 X0 sF2
       grind)
    | (have i₁ := eq24783
       have i₂ := eq379 sF2 x
       grind)
    | exact superpose eq379 eq24783
    | exact resolve eq24783 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25062 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq24783 eq409
    | exact resolve eq409 eq24783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24783
  have eq25208 : ∀ X1 : G, (σ x) = (k X1 X1) ∨ (σ x) = X1 ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq12979 x X1
       have i₂ := eq25031 x
       grind)
    | (have i₁ := eq12979 x X1
       have i₂ := eq25031 x
       grind)
    | exact superpose eq25031 eq12979
    | (have j0 := eq12979 x x
       grind)
    | exact resolve eq12979 eq25031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25258 : x ≠ (σ x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  have eq25259 : y ≠ (σ x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  have eq26744 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq25208 x
       grind)
    | exact superpose eq25208 eq44
    | (have j1 := eq25208 x
       grind)
    | exact resolve eq44 eq25208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26754 : (k (σ y) (σ y)) = (σ (σ x)) ∨ y = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq25208 y
       grind)
    | exact superpose eq25208 eq71
    | (have j1 := eq25208 y
       grind)
    | exact resolve eq71 eq25208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25208
  have eq26851 : (k (σ y) (σ y)) = (σ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq26754
       have r₂ := eq25259
       grind)
    | exact resolve eq26754 eq25259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25259 eq26754
  have eq26860 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq26744
       have r₂ := eq25258
       grind)
    | exact resolve eq26744 eq25258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26744
  have eq26931 : (k y y) = (τ (σ (σ x))) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26851 eq100
    | exact resolve eq100 eq26851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26851
  have eq26994 : (σ x) = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26931
       have i₂ := eq16 sF2
       grind)
    | exact superpose eq16 eq26931
    | exact resolve eq26931 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26931
  have eq27091 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26860 eq25062
    | exact resolve eq25062 eq26860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25062 eq26860
  have eq27119 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq27091
  have eq27300 : (σ x) = (σ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27119 eq25031
    | exact resolve eq25031 eq27119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25031 eq27119
  have eq27301 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq27300
  have eq27359 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq379 X0 x
       have i₂ := eq27301
       grind)
    | exact superpose eq27301 eq379
    | exact resolve eq379 eq27301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27371 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq409 x x
       have i₂ := eq27301
       grind)
    | exact superpose eq27301 eq409
    | exact resolve eq409 eq27301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27301
  have eq28594 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq27371 y
       grind)
    | exact superpose eq27371 eq71
    | exact resolve eq71 eq27371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27371
  have eq31169 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq28594
       have i₂ := eq27359 y
       grind)
    | exact superpose eq27359 eq28594
    | exact resolve eq28594 eq27359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28594
  have eq31249 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq31169
  have eq31295 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq31249
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31249
    | exact resolve eq31249 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31249
  have eq31361 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq31295 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq31295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31295
  have eq31362 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq31361
  have eq31492 : y = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq31362 eq27359
    | exact resolve eq27359 eq31362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27359 eq31362
  have eq31495 : x = (M.op x x) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq31492
  have eq31522 : ∀ X0 : G, x = (M.op X0 X0) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq31495
       have i₂ := eq379 X0 x
       grind)
    | (have i₁ := eq31495
       have i₂ := eq379 x X0
       grind)
    | exact superpose eq379 eq31495
    | exact resolve eq31495 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31538 : (k x x) = (M.op x x) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq31495
  have eq31750 : ∀ X1 : G, x = (k X1 X1) ∨ x = X1 ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    intro X1
    first
    | (have i₁ := eq12979 x X1
       have i₂ := eq31522 x
       grind)
    | exact superpose eq31522 eq12979
    | exact resolve eq12979 eq31522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12979
  have eq32519 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq31538
       grind)
    | exact superpose eq31538 eq44
    | exact resolve eq44 eq31538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31538
  have eq38582 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq32519
       have i₂ := eq31522 x
       grind)
    | exact superpose eq31522 eq32519
    | exact resolve eq32519 eq31522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31522 eq32519
  have eq38672 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq38582
  have eq38725 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq38672
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38672
    | exact resolve eq38672 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38672
  have eq38813 : x = (σ x) ∨ x = (σ x) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq38725 eq31750
    | (have j0 := eq31750 (σ x)
       grind)
    | exact resolve eq31750 eq38725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31750 eq38725
  have eq38816 : (σ x) = (σ (σ x)) ∨ y = (σ y) ∨ x = (σ x) := by grind
  clear eq38813
  have eq38862 : (σ x) = (τ (σ x)) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq38816 eq16
    | exact resolve eq16 eq38816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38816
  have eq38930 : x = (σ x) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq38862
    | exact resolve eq38862 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38862
  have eq38931 : y = (σ y) ∨ x = (σ x) := by grind
  clear eq38930
  have eq38936 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq38931 eq37
    | exact resolve eq37 eq38931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq38937 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq38931 eq41
    | exact resolve eq41 eq38931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq38948 : (k y y) = (τ (k y y)) ∨ x = (σ x) := by
    first
    | exact superpose eq38931 eq100
    | exact resolve eq100 eq38931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq38931
  have eq39599 : (σ x) = (τ (σ x)) ∨ x = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq38948
       have i₂ := eq26994
       grind)
    | exact superpose eq26994 eq38948
    | exact resolve eq38948 eq26994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26994
  have eq39676 : (σ x) = (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq39599
       have r₂ := eq25258
       grind)
    | exact resolve eq39599 eq25258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39599
  have eq39679 : x = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq39676
    | exact resolve eq39676 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39676
  have eq39681 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq39679
       have r₂ := eq25258
       grind)
    | exact resolve eq39679 eq25258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25258 eq39679
  have eq39854 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq39681
       have i₂ := eq379 X0 x
       grind)
    | (have i₁ := eq39681
       have i₂ := eq379 x x
       grind)
    | exact superpose eq379 eq39681
    | exact resolve eq39681 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39890 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq379 X0 x
       have i₂ := eq39681
       grind)
    | exact superpose eq39681 eq379
    | exact resolve eq379 eq39681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39903 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq409 x x
       have i₂ := eq39681
       grind)
    | exact superpose eq39681 eq409
    | exact resolve eq409 eq39681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39959 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq39681
  have eq40194 : ∀ X0 X1 : G, x = (M.op X0 X0) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq379 X1 X0
       have i₂ := eq39854 X0
       grind)
    | exact superpose eq39854 eq379
    | (have j1 := eq39854 X1
       grind)
    | exact resolve eq379 eq39854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40335 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq86
       have i₂ := eq39854 x
       grind)
    | exact superpose eq39854 eq86
    | (have j1 := eq39854 x
       grind)
    | exact resolve eq86 eq39854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq39854
  have eq40364 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq40335
       have r₂ := eq39959
       grind)
    | exact resolve eq40335 eq39959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39959 eq40335
  have eq40382 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40364
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40364
    | exact resolve eq40364 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40364
  have eq41025 : ∀ X0 X1 : G, (k x X0) = (M.op x X0) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    grind
  clear eq40194
  have eq41796 : (τ (σ y)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40382 eq50
    | exact resolve eq50 eq40382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq40382
  have eq41873 : y = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq41796
    | exact resolve eq41796 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41796
  have eq46762 : ∀ X0 : G, (τ (σ (k y X0))) = (k (τ y) X0) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq265 y X0
       have i₂ := eq38936 X0
       grind)
    | exact superpose eq38936 eq265
    | exact resolve eq265 eq38936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq38936
  have eq46782 : ∀ X0 : G, (k y X0) = (k (τ y) X0) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq46762 X0
       have i₂ := eq16 (k y X0)
       grind)
    | exact superpose eq16 eq46762
    | exact resolve eq46762 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46762
  have eq48880 : ∀ X0 : G, (k X0 y) = (σ (k (τ X0) y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq38937 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38937
    | exact resolve eq38937 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38937
  have eq49045 : ∀ X0 : G, (k X0 y) = (k X0 (σ y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq48880 X0
       have i₂ := eq35 X0 y
       grind)
    | exact superpose eq35 eq48880
    | exact resolve eq48880 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq48880
  have eq49066 : ∀ X0 : G, (k X0 y) = (k X0 (σ y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq49045 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq49045
    | (have j0 := eq49045 X0
       grind)
    | exact resolve eq49045 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49045
  have eq49216 : (k y (σ y)) = (k (τ y) y) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq49066 eq46782
    | exact resolve eq46782 eq49066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46782 eq49066
  have eq49277 : (k y (σ y)) = (k (τ y) y) ∨ x = (σ x) := by grind
  clear eq49216
  have eq49329 : (k y (σ y)) = (τ (k y (σ y))) ∨ x = (σ x) := by
    first
    | (have i₁ := eq49277
       have i₂ := eq555 y
       grind)
    | exact superpose eq555 eq49277
    | exact resolve eq49277 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq49277
  have eq50011 : (k y (σ y)) = (σ (k y (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq49329 eq15
    | exact resolve eq15 eq49329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49329
  have eq55325 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq39903 y
       grind)
    | exact superpose eq39903 eq71
    | exact resolve eq71 eq39903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39903
  have eq64865 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq45
       have i₂ := eq41025 y X0
       grind)
    | exact superpose eq41025 eq45
    | (have j1 := eq41025 X0 X0
       grind)
    | exact resolve eq45 eq41025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41025
  have eq64904 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq64865 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq64865
    | (have j0 := eq64865 X0
       grind)
    | exact resolve eq64865 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64865
  have eq64953 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq21 eq64904
    | (have j0 := eq64904 X0
       grind)
    | exact resolve eq64904 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64904
  have eq129666 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq55325
       have i₂ := eq39890 y
       grind)
    | exact superpose eq39890 eq55325
    | exact resolve eq55325 eq39890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55325
  have eq129769 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq129666
  have eq129824 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq129769
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq129769
    | exact resolve eq129769 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129769
  have eq129935 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq129824 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq129824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129824
  have eq129936 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq129935
  have eq130120 : y = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq129936 eq39890
    | exact resolve eq39890 eq129936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39890 eq129936
  have eq130125 : x = (M.op x x) ∨ y = (σ y) := by grind
  clear eq130120
  have eq131019 : ∀ X0 : G, x = (M.op X0 X0) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq130125
       have i₂ := eq379 X0 x
       grind)
    | (have i₁ := eq130125
       have i₂ := eq379 x X0
       grind)
    | exact superpose eq379 eq130125
    | exact resolve eq130125 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131043 : (k x x) = (M.op x x) ∨ y = (σ y) := by grind
  have eq131067 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq409 x x
       have i₂ := eq130125
       grind)
    | exact superpose eq130125 eq409
    | exact resolve eq409 eq130125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130125
  have eq135995 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq131043
       grind)
    | exact superpose eq131043 eq44
    | exact resolve eq44 eq131043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq131043
  have eq137112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq131067 y
       grind)
    | exact superpose eq131067 eq45
    | exact resolve eq45 eq131067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131067
  have eq137251 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq137112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq137112
    | exact resolve eq137112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137112
  have eq137349 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq21 eq137251
    | exact resolve eq137251 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137251
  have eq159707 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq135995
       have i₂ := eq131019 x
       grind)
    | exact superpose eq131019 eq135995
    | exact resolve eq135995 eq131019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131019 eq135995
  have eq159840 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) := by grind
  clear eq159707
  have eq159911 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq159840
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq159840
    | exact resolve eq159840 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159840
  have eq160033 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq159911 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq159911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159911
  have eq160034 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by grind
  clear eq160033
  have eq161089 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq160034 eq409
    | exact resolve eq409 eq160034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq160034
  have eq180479 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5783 x
       have i₂ := eq41873
       grind)
    | exact superpose eq41873 eq5783
    | (have j0 := eq5783 x
       grind)
    | exact resolve eq5783 eq41873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5783 eq41873
  have eq180746 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq180479
  have eq180872 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq180746
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq180746
    | exact resolve eq180746 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq180746
  have eq195420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq161089 eq137349
    | exact resolve eq137349 eq161089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137349 eq161089
  have eq195426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq195420
  have eq195529 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq27 eq195426
    | exact resolve eq195426 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195426
  have eq195576 : y = (σ y) := by
    first
    | (have r₁ := eq195529
       have r₂ := eq28
       grind)
    | exact resolve eq195529 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195529
  have eq195584 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq195576 eq27
    | exact resolve eq27 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq195585 : y = (τ y) := by
    first
    | exact superpose eq195576 eq30
    | exact resolve eq30 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq195590 : (k x y) = (τ (k (σ x) y)) := by
    first
    | exact superpose eq195576 eq57
    | exact resolve eq57 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq195752 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) y) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq195576 eq64953
    | (have j0 := eq64953 X0
       grind)
    | exact resolve eq64953 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64953
  have eq219908 : y = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq195576 eq180872
    | exact resolve eq180872 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180872
  have eq219914 : ∀ X0 : G, y = (σ (M.op X0 X0)) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq219908
       have i₂ := eq379 X0 x
       grind)
    | (have i₁ := eq219908
       have i₂ := eq379 x x
       grind)
    | exact superpose eq379 eq219908
    | exact resolve eq219908 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq219908
  have eq220437 : ∀ X1 : G, y = (σ (k (σ y) (σ y))) ∨ x = (k (σ y) (σ y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq219914 X1
       have i₂ := eq13166 x X1
       grind)
    | (have i₁ := eq219914 x
       have i₂ := eq13166 x X1
       grind)
    | exact superpose eq13166 eq219914
    | (have j1 := eq13166 X1 X1
       grind)
    | exact resolve eq219914 eq13166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13166 eq219914
  have eq220773 : ∀ X1 : G, y = (σ (k y y)) ∨ x = (k (σ y) (σ y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X1
    first
    | exact superpose eq195576 eq220437
    | (have j0 := eq220437 X1
       grind)
    | exact resolve eq220437 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220437
  have eq220805 : ∀ X1 : G, y = (k (σ y) (σ y)) ∨ x = (k (σ y) (σ y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq220773 X1
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq220773
    | (have j0 := eq220773 X1
       grind)
    | exact resolve eq220773 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220773
  have eq220812 : ∀ X1 : G, y = (k y y) ∨ x = (k (σ y) (σ y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X1
    first
    | exact superpose eq195576 eq220805
    | (have j0 := eq220805 X1
       grind)
    | exact resolve eq220805 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220805
  have eq220817 : ∀ X1 : G, x = (k y y) ∨ y = (k y y) ∨ (M.op X1 X1) = (σ y) := by
    intro X1
    first
    | exact superpose eq195576 eq220812
    | (have j0 := eq220812 X1
       grind)
    | exact resolve eq220812 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220812
  have eq220820 : ∀ X1 : G, (M.op X1 X1) = y ∨ x = (k y y) ∨ y = (k y y) := by
    intro X1
    first
    | exact superpose eq195576 eq220817
    | exact resolve eq220817 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220817
  have eq220823 : ∀ X1 : G, x = (k y y) ∨ (M.op X1 X1) = y := by
    intro X1
    first
    | (have j0 := eq220820 X1
       have j1 := eq13656 X1 y
       grind)
    | (have r₁ := eq220820 X1
       have r₂ := eq13656 x y
       grind)
    | exact resolve eq220820 eq13656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13656 eq220820
  have eq221302 : ∀ X0 : G, (σ x) = (k (σ y) (σ y)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq71
       have i₂ := eq220823 X0
       grind)
    | exact superpose eq220823 eq71
    | (have j1 := eq220823 X0
       grind)
    | exact resolve eq71 eq220823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq220823
  have eq221428 : ∀ X0 : G, (σ x) = (k y y) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq195576 eq221302
    | (have j0 := eq221302 X0
       grind)
    | exact resolve eq221302 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221302
  have eq221464 : ∀ X0 : G, (σ x) = (k y y) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq221428 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq221428
    | (have j0 := eq221428 X0
       grind)
    | exact resolve eq221428 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221428
  have eq227312 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ x = (σ x) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38948
       have i₂ := eq221464 X0
       grind)
    | exact superpose eq221464 eq38948
    | (have j1 := eq221464 X0
       grind)
    | exact resolve eq38948 eq221464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38948 eq221464
  have eq227408 : ∀ X0 : G, x = (σ x) ∨ x = (σ x) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq29 eq227312
    | (have j0 := eq227312 X0
       grind)
    | exact resolve eq227312 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227312
  have eq227409 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq227408 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227408
  have eq227595 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = (σ x) := by
    intro X0
    grind
  have eq230824 : (M.op y (σ y)) = (σ (M.op y (σ y))) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq50011
       have i₂ := eq227595 sF3
       grind)
    | exact superpose eq227595 eq50011
    | exact resolve eq50011 eq227595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50011 eq227595
  have eq230861 : (M.op y (σ y)) = (σ (M.op y (σ y))) ∨ x = (σ x) := by grind
  clear eq230824
  have eq230923 : (M.op y y) = (σ (M.op y y)) ∨ x = (σ x) := by
    first
    | exact superpose eq195576 eq230861
    | exact resolve eq230861 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230861
  have eq550179 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x y)) ∨ x = (M.op X0 X0) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq7372 X0
       have i₂ := eq227409 (M.op X0 X0)
       grind)
    | exact superpose eq227409 eq7372
    | (have j0 := eq7372 X0
       grind)
    | exact resolve eq7372 eq227409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550457 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op X0 X0) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq550179 X0
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq550179
    | (have j0 := eq550179 X0
       grind)
    | exact resolve eq550179 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550179
  have eq550530 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) y) ∨ x = (M.op X0 X0) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq195576 eq550457
    | (have j0 := eq550457 X0
       grind)
    | exact resolve eq550457 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550457
  have eq550566 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) y) ∨ x = (M.op X0 X0) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq550530 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq550530
    | (have j0 := eq550530 X0
       grind)
    | exact resolve eq550530 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550530
  have eq550592 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) y) ∨ x = (M.op X0 X0) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq21 eq550566
    | (have j0 := eq550566 X0
       grind)
    | exact resolve eq550566 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550566
  have eq714672 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = X0 ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq7214 X0 X0 x
       have i₂ := eq227409 (M.op X0 X0)
       grind)
    | exact superpose eq227409 eq7214
    | exact resolve eq7214 eq227409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7214 eq227409
  have eq1373929 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) y) ∨ x = (M.op X0 X0) ∨ x = (σ x) ∨ y = (σ x) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq550592 X0
       have i₂ := eq714672 sF2
       grind)
    | exact superpose eq714672 eq550592
    | (have j0 := eq550592 X0
       have j1 := eq714672 (σ x)
       grind)
    | exact resolve eq550592 eq714672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550592 eq714672
  have eq1374205 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) y) ∨ x = (M.op X0 X0) ∨ x = (σ x) ∨ y = (σ x) := by
    intro X0
    first
    | (have j0 := eq1373929 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373929
  have eq1374429 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op X0 X0) ∨ x = (σ x) ∨ y = (σ x) := by
    intro X0
    first
    | exact superpose eq195584 eq1374205
    | (have j0 := eq1374205 X0
       grind)
    | exact resolve eq1374205 eq195584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374205
  have eq1374682 : ∀ X0 : G, x = (M.op X0 X0) ∨ x = (σ x) ∨ y = (σ x) := by
    intro X0
    first
    | (have j0 := eq1374429 X0
       grind)
    | (have r₁ := eq1374429 X0
       have r₂ := eq28
       grind)
    | exact resolve eq1374429 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374429
  have eq1376279 : x = (σ x) ∨ x = (σ x) ∨ x = (σ x) ∨ y = (σ x) := by
    first
    | (have i₁ := eq230923
       have i₂ := eq1374682 y
       grind)
    | exact superpose eq1374682 eq230923
    | exact resolve eq230923 eq1374682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230923 eq1374682
  have eq1376435 : x = (σ x) ∨ x = (σ x) ∨ y = (σ x) := by grind
  clear eq1376279
  have eq1376736 : x = (σ x) ∨ x = (σ x) ∨ y = (σ x) := by
    first
    | (have i₁ := eq1376435
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1376435
    | exact resolve eq1376435 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376435
  have eq1376737 : y = (σ x) ∨ x = (σ x) := by grind
  clear eq1376736
  have eq1377126 : x = (τ y) ∨ x = (σ x) := by
    first
    | exact superpose eq1376737 eq29
    | exact resolve eq29 eq1376737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1377572 : x ≠ y ∨ x = (σ x) := by grind
  clear eq1376737
  have eq1377699 : x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq1377126
       have i₂ := eq195585
       grind)
    | exact superpose eq195585 eq1377126
    | exact resolve eq1377126 eq195585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195585 eq1377126
  have eq1377780 : x = (σ x) := by
    first
    | (have r₁ := eq1377699
       have r₂ := eq1377572
       grind)
    | exact resolve eq1377699 eq1377572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377572 eq1377699
  have eq1378054 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1377780 eq195584
    | exact resolve eq195584 eq1377780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195584
  have eq1378055 : (k x y) = (τ (k x y)) := by
    first
    | exact superpose eq1377780 eq195590
    | exact resolve eq195590 eq1377780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195590
  have eq1378081 : ∀ X0 : G, (σ (M.op x y)) = (k x y) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq1377780 eq195752
    | (have j0 := eq195752 X0
       grind)
    | exact resolve eq195752 eq1377780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195752
  have eq1378126 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1378054
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1378054
    | exact resolve eq1378054 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378054
  have eq1378184 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1378126 eq28
    | exact resolve eq28 eq1378126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1378126
  have eq1387839 : ∀ X0 : G, (σ (M.op x y)) = (τ (σ (M.op x y))) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1378055
       have i₂ := eq1378081 X0
       grind)
    | exact superpose eq1378081 eq1378055
    | (have j1 := eq1378081 X0
       grind)
    | exact resolve eq1378055 eq1378081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378081
  have eq1387855 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq31 eq1387839
    | (have j0 := eq1387839 X0
       grind)
    | exact resolve eq1387839 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387839
  have eq1387882 : ∀ X0 : G, y = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq1387855 X0
       grind)
    | (have r₁ := eq1387855 X0
       have r₂ := eq1378184
       grind)
    | exact resolve eq1387855 eq1378184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387855
  have eq1389056 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x y)) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7372 X0
       have i₂ := eq1387882 (M.op X0 X0)
       grind)
    | exact superpose eq1387882 eq7372
    | (have j0 := eq7372 X0
       grind)
    | exact resolve eq7372 eq1387882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7372
  have eq1389952 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1389056 X0
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq1389056
    | (have j0 := eq1389056 X0
       grind)
    | exact resolve eq1389056 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1389056
  have eq1391022 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) y) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq195576 eq1389952
    | (have j0 := eq1389952 X0
       grind)
    | exact resolve eq1389952 eq195576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195576 eq1389952
  have eq1391796 : ∀ X0 : G, (σ (M.op x y)) = (k x y) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq1377780 eq1391022
    | (have j0 := eq1391022 X0
       grind)
    | exact resolve eq1391022 eq1377780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391022
  have eq1392359 : ∀ X0 : G, (σ (M.op x y)) = (k x y) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1391796 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1391796
    | (have j0 := eq1391796 X0
       grind)
    | exact resolve eq1391796 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391796
  have eq1392654 : ∀ X0 : G, (σ (M.op x y)) = (k x y) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq21 eq1392359
    | (have j0 := eq1392359 X0
       grind)
    | exact resolve eq1392359 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392359
  have eq1392781 : (σ (M.op x y)) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq1392654 x
       have i₂ := eq1387882 x
       grind)
    | exact superpose eq1387882 eq1392654
    | exact resolve eq1392654 eq1387882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392654
  have eq1451538 : (σ (M.op x y)) = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq1378055
       have i₂ := eq1392781
       grind)
    | exact superpose eq1392781 eq1378055
    | exact resolve eq1378055 eq1392781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378055 eq1392781
  have eq1451557 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31 eq1451538
    | exact resolve eq1451538 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1451538
  have eq1451588 : x = y := by
    first
    | (have r₁ := eq1451557
       have r₂ := eq1378184
       grind)
    | exact resolve eq1451557 eq1378184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451557
  have eq1451642 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1451588
       grind)
    | exact superpose eq1451588 eq19
    | exact resolve eq19 eq1451588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1452661 : y = (M.op x y) := by
    first
    | (have i₁ := eq1451642
       have i₂ := eq1387882 x
       grind)
    | exact superpose eq1387882 eq1451642
    | exact resolve eq1451642 eq1387882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387882 eq1451642
  have eq1452882 : x = (M.op x y) := by
    first
    | (have i₁ := eq1452661
       have i₂ := eq1451588
       grind)
    | exact superpose eq1451588 eq1452661
    | exact resolve eq1452661 eq1451588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451588 eq1452661
  have eq1453488 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1452882 eq21
    | exact resolve eq21 eq1452882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1453906 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1453488
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1453488
    | exact resolve eq1453488 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1453488
  have eq1454091 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq1377780 eq1453906
    | exact resolve eq1453906 eq1377780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377780 eq1453906
  have eq1454645 : x ≠ (M.op x y) := by
    first
    | exact superpose eq1454091 eq1378184
    | exact resolve eq1378184 eq1454091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378184 eq1454091
  have eq1454649 : False := by grind
  exact eq1454649

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pxx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq50 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 X2) (M.op X3 X3)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X1 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq20 X0 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 X2) (M.op X3 X3)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq91 X0 X1 X2 X3
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq91 (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X2 X2) (M.op X3 X3)) X2 X3
       have r₂ := eq12 X0 (M.op (M.op X2 X2) (M.op X3 X3))
       grind)
    | (have r₁ := eq91 X1 X1 X1 X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq91 X0 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq168 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1115 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ (M.op X2 X3) ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq168 X2 X3
       have i₂ := eq20 X0 X2 X1
       grind)
    | (have i₁ := eq168 (M.op X2 X2) X1
       have i₂ := eq20 X2 X1 X2
       grind)
    | exact superpose eq20 eq168
    | (have j0 := eq168 X2 X3
       grind)
    | (have r₁ := eq168 (M.op X2 X2) (M.op X2 X2)
       have r₂ := eq20 X2 (M.op X2 X2) X2
       grind)
    | (have r₁ := eq168 (M.op X0 X0) (M.op X2 X2)
       have r₂ := eq20 X0 (M.op X0 X0) X2
       grind)
    | exact resolve eq168 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq168
  have eq1130 : ∀ X2 X3 : G, (M.op X2 X3) = (k X2 X3) := by
    intro X2 X3
    first
    | (have j0 := eq1115 x x X2 X3
       have j1 := eq130 X2 X3 X2 X3
       grind)
    | (have r₁ := eq1115 x x (M.op X2 X2) (M.op X3 X3)
       have r₂ := eq130 (M.op x x) (M.op x x) X2 X3
       grind)
    | (have r₁ := eq1115 X2 X3 x x
       have r₂ := eq130 x x X2 X3
       grind)
    | exact resolve eq1115 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq1115
  have eq33152 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1130 (σ X0) (σ X1)
       grind)
    | exact superpose eq1130 eq15
    | exact resolve eq15 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33171 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33152 X0 X1
       have i₂ := eq1130 X0 X1
       grind)
    | exact superpose eq1130 eq33152
    | exact resolve eq33152 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq33152
  have eq33195 : False := by grind
  exact eq33195

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyx_y_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq177 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = (M.op (M.op (M.op X0 X0) (M.op x y)) x) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq184 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq539 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq175 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq539 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq539 X2 X0
       grind)
    | exact superpose eq539 eq16
    | exact resolve eq16 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq539 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq539 (M.op X1 X1) X0
       grind)
    | exact superpose eq539 eq16
    | exact resolve eq16 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X1
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq180 X0
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq180
    | exact resolve eq180 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq180 (M.op (M.op X1 X1) x)
       have i₂ := eq16 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X0 X1
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq175
    | exact resolve eq175 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq571 X0 X1
       have i₂ := eq564 X0 X0 X1
       grind)
    | exact superpose eq564 eq571
    | exact resolve eq571 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq646 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (k (M.op X0 X0) X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq572 X1 X2
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq572 X1 X2
       have i₂ := eq539 X1 X0
       grind)
    | exact superpose eq539 eq572
    | exact resolve eq572 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq572 X1 (k (M.op X1 X1) X1)
       have i₂ := eq539 X0 (k (M.op X1 X1) X1)
       grind)
    | (have i₁ := eq572 X1 (k (M.op X1 X1) X1)
       have i₂ := eq539 (k (M.op X1 X1) X1) X0
       grind)
    | exact superpose eq539 eq572
    | exact resolve eq572 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq670 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq576 X1 (M.op X2 X2)
       have i₂ := eq540 X0 X1 X2
       grind)
    | (have i₁ := eq576 X0 (M.op X0 X0)
       have i₂ := eq540 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq540 eq576
    | exact resolve eq576 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) = (k (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq576 X1 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))
       have i₂ := eq175 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq175 eq576
    | exact resolve eq576 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq576 X1 (M.op X1 X1)
       have i₂ := eq539 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq576 X1 (M.op X1 X1)
       have i₂ := eq539 (M.op X1 X1) X0
       grind)
    | exact superpose eq539 eq576
    | exact resolve eq576 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) X0) = (M.op X0 (k (M.op X2 X2) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq671 X0 X1 X2
       have i₂ := eq570 X2 (M.op X1 X1)
       grind)
    | exact superpose eq570 eq671
    | exact resolve eq671 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq685 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (k (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq680 X0 X1 X2
       have i₂ := eq676 X1 X2
       grind)
    | exact superpose eq676 eq680
    | exact resolve eq680 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq689 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) (M.op X4 X4)) = X3 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq564 X4 x X3
       have i₂ := eq540 x X0 X1
       grind)
    | (have i₁ := eq564 X0 (M.op x x) x
       have i₂ := eq540 X0 x x
       grind)
    | exact superpose eq540 eq564
    | exact resolve eq564 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq721 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq564 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq564 eq175
    | exact resolve eq175 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq748 : ∀ X0 X1 X3 X4 : G, (k (M.op X4 X4) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)) = X3 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq689 X0 X1 X3 X4
       have i₂ := eq570 X4 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)
       grind)
    | exact superpose eq570 eq689
    | exact resolve eq689 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq751 : ∀ X0 X1 X3 X4 : G, (k (M.op X4 X4) (M.op (k (M.op X1 X1) (M.op X0 X0)) X3)) = X3 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq748 X0 X1 X3 X4
       have i₂ := eq570 X1 (M.op X0 X0)
       grind)
    | exact superpose eq570 eq748
    | exact resolve eq748 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq752 : ∀ X1 X3 X4 : G, (k (M.op X4 X4) (M.op (M.op X1 X1) X3)) = X3 := by
    intro X1 X3 X4
    first
    | (have i₁ := eq751 x X1 X3 X4
       have i₂ := eq676 x X1
       grind)
    | exact superpose eq676 eq751
    | exact resolve eq751 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq925 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (k (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq568 X1 X0 X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq568
    | exact resolve eq568 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1001 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (k (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq568 X2 X0 X1
       have i₂ := eq570 X0 X1
       grind)
    | exact superpose eq570 eq568
    | exact resolve eq568 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq1376 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X1) = (k (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq646 X2 X1 (k (M.op X2 X2) X1)
       have i₂ := eq685 X1 X0 (k (M.op X2 X2) X1)
       grind)
    | exact superpose eq685 eq646
    | exact resolve eq646 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq685
  have eq1502 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
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
  have eq1503 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1537 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq11
    | (have j0 := eq11 (k X1 X1) X0
       grind)
    | exact resolve eq11 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1544 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  clear eq18
  have eq1545 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1605 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1639 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1537 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq2810 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq539 X2 X1
       have i₂ := eq1639 X2 X0
       grind)
    | exact superpose eq1639 eq539
    | (have j1 := eq1639 X1 X0
       grind)
    | exact resolve eq539 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2887 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1639 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq3137 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1544
       grind)
    | exact superpose eq1544 eq40
    | exact resolve eq40 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq3138 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3137
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3137
    | exact resolve eq3137 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3137
  have eq3140 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3138
    | exact resolve eq3138 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3138
  have eq3406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3140 eq1545
    | exact resolve eq1545 eq3140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3413 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3406
       have r₂ := eq27
       grind)
    | exact resolve eq3406 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq3432 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq3413 eq539
    | exact resolve eq539 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3447 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ x) (M.op X1 X1)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq3413 eq670
    | exact resolve eq670 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3449 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq3413 eq676
    | exact resolve eq676 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3413
  have eq3490 : (σ x) = (k (σ x) (k x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2810 eq3449
    | (have j1 := eq2810 x x y
       grind)
    | exact resolve eq3449 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449
  have eq3492 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (k x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2810 eq3447
    | (have j1 := eq2810 (k (σ x) (k x x)) x X0
       grind)
    | exact resolve eq3447 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447
  have eq3513 : (k x x) = (k (σ x) (k x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2810 eq3492
    | (have j1 := eq2810 x x y
       grind)
    | exact resolve eq3492 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3492
  have eq3525 : (σ x) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3490 eq3513
    | exact resolve eq3513 eq3490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3490 eq3513
  have eq3608 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq651 X0 (M.op X0 X0)
       have i₂ := eq3432 (M.op X0 X0)
       grind)
    | exact superpose eq3432 eq651
    | exact resolve eq651 eq3432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3636 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3432 eq3608
    | exact resolve eq3608 eq3432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432 eq3608
  have eq3720 : (k (σ x) (σ x)) = (σ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3525
       grind)
    | exact superpose eq3525 eq39
    | exact resolve eq39 eq3525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3525
  have eq3724 : (k (σ x) (σ x)) = (σ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3720
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3720
    | exact resolve eq3720 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq3726 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq3636 eq3724
    | exact resolve eq3724 eq3636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq3744 : ∀ X0 : G, x = (M.op X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq539 y X0
       have i₂ := eq3726
       grind)
    | exact superpose eq3726 eq539
    | exact resolve eq539 eq3726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3762 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq676 y X0
       have i₂ := eq3726
       grind)
    | exact superpose eq3726 eq676
    | exact resolve eq676 eq3726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3775 : ∀ X0 X1 : G, (k x X1) = (k (M.op X0 X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 X1 y
       have i₂ := eq3726
       grind)
    | exact superpose eq3726 eq1376
    | exact resolve eq1376 eq3726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3726
  have eq3791 : ∀ X0 : G, (M.op X0 X0) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | exact superpose eq3775 eq3762
    | exact resolve eq3762 eq3775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3762 eq3775
  have eq3806 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq3744 eq3791
    | exact resolve eq3791 eq3744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq4501 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3806
       grind)
    | exact superpose eq3806 eq39
    | exact resolve eq39 eq3806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq4511 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq4501
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4501
    | exact resolve eq4501 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4501
  have eq4518 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq4511 eq1605
    | (have j0 := eq1605 (σ x) (σ x)
       grind)
    | (have r₁ := eq1605 (σ x) (σ x)
       have r₂ := eq4511
       grind)
    | exact resolve eq1605 eq4511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4511
  have eq4519 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq4518
  have eq4520 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq4519
  have eq4581 : x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq4520 eq3744
    | exact resolve eq3744 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3744 eq4520
  have eq4584 : (σ x) = (σ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) := by grind
  clear eq4581
  have eq4671 : (σ x) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq4584 eq15
    | exact resolve eq15 eq4584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4584
  have eq4688 : x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq4671
    | exact resolve eq4671 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq4689 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4688
  have eq5035 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3636 eq141
    | exact resolve eq141 eq3636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3636
  have eq5043 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq5035
    | exact resolve eq5035 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035
  have eq5046 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq2887 y x
       grind)
    | (have r₁ := eq5043
       have r₂ := eq2887 x x
       grind)
    | exact resolve eq5043 eq2887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5043
  have eq5049 : (σ x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4689 eq5046
    | exact resolve eq5046 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5046
  have eq5068 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (σ x) (M.op x y)) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0
       have i₂ := eq5049
       grind)
    | exact superpose eq5049 eq182
    | exact resolve eq182 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5071 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq539 y X0
       have i₂ := eq5049
       grind)
    | exact superpose eq5049 eq539
    | exact resolve eq539 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5076 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq564 y X0 X1
       have i₂ := eq5049
       grind)
    | exact superpose eq5049 eq564
    | exact resolve eq564 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5083 : ∀ X0 : G, (k (σ x) (M.op (σ x) X0)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq576 y x
       have i₂ := eq5049
       grind)
    | exact superpose eq5049 eq576
    | exact resolve eq576 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq5092 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq721 X1 X0 y
       have i₂ := eq5049
       grind)
    | exact superpose eq5049 eq721
    | exact resolve eq721 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5098 : ∀ X0 X1 : G, (M.op (σ x) (k (M.op X0 X0) X1)) = X1 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1001 X0 X1 y
       have i₂ := eq5049
       grind)
    | exact superpose eq5049 eq1001
    | exact resolve eq1001 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5102 : ∀ X0 X1 : G, (k (σ x) X1) = (k (M.op X0 X0) X1) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 X1 y
       have i₂ := eq5049
       grind)
    | exact superpose eq5049 eq1376
    | exact resolve eq1376 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5049
  have eq5123 : ∀ X1 : G, (M.op (σ x) (k (σ x) X1)) = X1 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq5102 eq5098
    | exact resolve eq5098 eq5102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5098 eq5102
  have eq5134 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq5092 eq5076
    | exact resolve eq5076 eq5092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5076 eq5092
  have eq5138 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4689 eq5068
    | exact resolve eq5068 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5068
  have eq5151 : (M.op (σ x) y) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5071 eq5138
    | exact resolve eq5138 eq5071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5071 eq5138
  have eq5154 : (M.op x y) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5134 eq5151
    | exact resolve eq5151 eq5134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5134 eq5151
  have eq5623 : (σ y) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5083
    | (have j0 := eq5083 (σ y)
       grind)
    | exact resolve eq5083 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5083
  have eq5688 : (τ (σ y)) = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5623 eq90
    | exact resolve eq90 eq5623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5623
  have eq5690 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq5688
    | exact resolve eq5688 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5688
  have eq5691 : y = (k (σ x) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4689 eq5690
    | exact resolve eq5690 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4689 eq5690
  have eq5788 : (τ (M.op (σ x) (σ y))) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5691 eq5123
    | exact resolve eq5123 eq5691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5123 eq5691
  have eq5808 : (τ (M.op (σ x) (σ y))) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5788
  have eq5812 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5154 eq5808
    | exact resolve eq5808 eq5154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154 eq5808
  have eq5822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5812 eq14
    | exact resolve eq14 eq5812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5812
  have eq5824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5822
    | exact resolve eq5822 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5822
  have eq5827 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5824
       have r₂ := eq27
       grind)
    | exact resolve eq5824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5824
  have eq5828 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5827 eq27
    | exact resolve eq27 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5831 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5827 eq1503
    | (have r₁ := eq1503
       have r₂ := eq5827
       grind)
    | exact resolve eq1503 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq5833 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5831
  have eq6273 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5833 eq3140
    | exact resolve eq3140 eq5833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3140
  have eq6277 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5833 eq90
    | exact resolve eq90 eq5833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5833
  have eq6284 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq6273
  have eq6289 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq6277
    | exact resolve eq6277 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6277
  have eq6291 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6284
       have r₂ := eq5828
       grind)
    | exact resolve eq6284 eq5828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5828 eq6284
  have eq6349 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6289 eq539
    | exact resolve eq539 eq6289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6367 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6289 eq676
    | exact resolve eq676 eq6289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6380 : ∀ X0 X1 : G, (k (σ x) X1) = (k (M.op X0 X0) X1) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6289 eq1376
    | exact resolve eq1376 eq6289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289
  have eq6409 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6380 eq6367
    | exact resolve eq6367 eq6380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6367 eq6380
  have eq6428 : (σ x) = (k (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6349 eq6409
    | exact resolve eq6409 eq6349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6349 eq6409
  have eq6456 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6291 eq539
    | exact resolve eq539 eq6291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6471 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ x) (M.op X1 X1)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6291 eq670
    | exact resolve eq670 eq6291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq6473 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 X0)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6291 eq676
    | exact resolve eq676 eq6291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6291
  have eq6530 : (σ x) = (k (σ x) (k x x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2810 eq6473
    | (have j1 := eq2810 x x y
       grind)
    | exact resolve eq6473 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6473
  have eq6532 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (k x x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2810 eq6471
    | (have j1 := eq2810 (k (σ x) (k x x)) x X0
       grind)
    | exact resolve eq6471 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6471
  have eq6558 : (k x x) = (k (σ x) (k x x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2810 eq6532
    | (have j1 := eq2810 x x y
       grind)
    | exact resolve eq6532 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810 eq6532
  have eq6572 : (σ x) = (k x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6530 eq6558
    | exact resolve eq6558 eq6530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6530 eq6558
  have eq6801 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6428 eq141
    | exact resolve eq141 eq6428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq6428
  have eq6812 : y = (k x y) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq6801
    | exact resolve eq6801 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801
  have eq6907 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 X0)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq651 X0 (M.op X0 X0)
       have i₂ := eq6456 (M.op X0 X0)
       grind)
    | exact superpose eq6456 eq651
    | exact resolve eq651 eq6456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq6955 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6456 eq6907
    | exact resolve eq6907 eq6456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6456 eq6907
  have eq7083 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq6572
       grind)
    | exact superpose eq6572 eq39
    | exact resolve eq39 eq6572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6572
  have eq7096 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7083
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7083
    | exact resolve eq7083 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7083
  have eq7098 : x = (M.op y y) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6955 eq7096
    | exact resolve eq7096 eq6955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6955 eq7096
  have eq7124 : ∀ X0 : G, x = (M.op X0 X0) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq539 y X0
       have i₂ := eq7098
       grind)
    | exact superpose eq7098 eq539
    | exact resolve eq539 eq7098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7142 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) x) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq676 y X0
       have i₂ := eq7098
       grind)
    | exact superpose eq7098 eq676
    | exact resolve eq676 eq7098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq7155 : ∀ X0 X1 : G, (k x X1) = (k (M.op X0 X0) X1) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 X1 y
       have i₂ := eq7098
       grind)
    | exact superpose eq7098 eq1376
    | exact resolve eq1376 eq7098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7098
  have eq7192 : ∀ X0 : G, (M.op X0 X0) = (k x x) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7155 eq7142
    | exact resolve eq7142 eq7155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7142 eq7155
  have eq7209 : x = (k x x) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7124 eq7192
    | exact resolve eq7192 eq7124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7192
  have eq7471 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq7209
       grind)
    | exact superpose eq7209 eq39
    | exact resolve eq39 eq7209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq7209
  have eq7485 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7471
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7471
    | exact resolve eq7471 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7471
  have eq7495 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7485 eq1605
    | (have j0 := eq1605 (σ x) (σ x)
       grind)
    | (have r₁ := eq1605 (σ x) (σ x)
       have r₂ := eq7485
       grind)
    | exact resolve eq1605 eq7485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605 eq7485
  have eq7496 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by grind
  clear eq7495
  have eq7497 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by grind
  clear eq7496
  have eq7569 : x = (σ x) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7497 eq7124
    | exact resolve eq7124 eq7497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7124 eq7497
  have eq7573 : (σ x) = (σ (σ x)) ∨ x = (σ x) ∨ y = (M.op x y) := by grind
  clear eq7569
  have eq7682 : (σ x) = (τ (σ x)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7573 eq15
    | exact resolve eq15 eq7573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7573
  have eq7701 : x = (σ x) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq7682
    | exact resolve eq7682 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7682
  have eq7702 : y = (M.op x y) ∨ x = (σ x) := by grind
  clear eq7701
  have eq9126 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1544
       have i₂ := eq6812
       grind)
    | exact superpose eq6812 eq1544
    | exact resolve eq1544 eq6812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544 eq6812
  have eq9132 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) := by grind
  clear eq9126
  have eq9138 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq2887 y x
       grind)
    | (have r₁ := eq9132
       have r₂ := eq2887 x x
       grind)
    | exact resolve eq9132 eq2887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2887 eq9132
  have eq9146 : (σ x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7702 eq9138
    | exact resolve eq9138 eq7702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9138
  have eq9172 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (σ x) (M.op x y)) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq182 y X0
       have i₂ := eq9146
       grind)
    | exact superpose eq9146 eq182
    | exact resolve eq182 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9173 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq184 y X0
       have i₂ := eq9146
       grind)
    | exact superpose eq9146 eq184
    | exact resolve eq184 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq9175 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq539 y X0
       have i₂ := eq9146
       grind)
    | exact superpose eq9146 eq539
    | exact resolve eq539 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9180 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq564 y X0 X1
       have i₂ := eq9146
       grind)
    | exact superpose eq9146 eq564
    | exact resolve eq564 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq9185 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq570 y x
       have i₂ := eq9146
       grind)
    | exact superpose eq9146 eq570
    | exact resolve eq570 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq9196 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq721 X1 X0 y
       have i₂ := eq9146
       grind)
    | exact superpose eq9146 eq721
    | exact resolve eq721 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq9202 : ∀ X0 X1 : G, (M.op (σ x) (k (M.op X0 X0) X1)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1001 X0 X1 y
       have i₂ := eq9146
       grind)
    | exact superpose eq9146 eq1001
    | exact resolve eq1001 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq9206 : ∀ X0 X1 : G, (k (σ x) X1) = (k (M.op X0 X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 X1 y
       have i₂ := eq9146
       grind)
    | exact superpose eq9146 eq1376
    | exact resolve eq1376 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376 eq9146
  have eq9242 : ∀ X1 : G, (M.op (σ x) (k (σ x) X1)) = X1 ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq9206 eq9202
    | exact resolve eq9202 eq9206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9202 eq9206
  have eq9253 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq9196 eq9180
    | exact resolve eq9180 eq9196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9180 eq9196
  have eq9256 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5827 eq9173
    | exact resolve eq9173 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9173
  have eq9257 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7702 eq9172
    | exact resolve eq9172 eq7702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9172
  have eq9271 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq9256
    | (have j0 := eq9256 X0
       grind)
    | exact resolve eq9256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9256
  have eq9272 : (M.op (σ x) y) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9175 eq9257
    | exact resolve eq9257 eq9175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9257
  have eq9276 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5827 eq9271
    | exact resolve eq9271 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9271
  have eq9277 : (M.op x y) = (M.op (σ x) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9253 eq9272
    | exact resolve eq9272 eq9253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9253 eq9272
  have eq9279 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9175 eq9276
    | exact resolve eq9276 eq9175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9175 eq9276
  have eq9280 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq9279
    | exact resolve eq9279 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9279
  have eq9281 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5827 eq9280
    | exact resolve eq9280 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5827 eq9280
  have eq9723 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9185 eq9281
    | exact resolve eq9281 eq9185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9185 eq9281
  have eq9724 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9723
  have eq9942 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9724 eq90
    | exact resolve eq90 eq9724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq9724
  have eq9953 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq9942
    | exact resolve eq9942 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9942
  have eq9958 : y = (k (σ x) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7702 eq9953
    | exact resolve eq9953 eq7702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7702 eq9953
  have eq10210 : y = (M.op (σ x) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9958 eq9242
    | exact resolve eq9242 eq9958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9242 eq9958
  have eq10245 : y = (M.op (σ x) y) ∨ y = (M.op x y) := by grind
  clear eq10210
  have eq10255 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9277 eq10245
    | exact resolve eq10245 eq9277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9277 eq10245
  have eq10256 : y = (M.op x y) := by grind
  clear eq10255
  have eq10262 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq10256
       grind)
    | exact superpose eq10256 eq24
    | exact resolve eq24 eq10256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq10266 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op (M.op X1 X1) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X1 X0
       have i₂ := eq10256
       grind)
    | exact superpose eq10256 eq182
    | exact resolve eq182 eq10256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq10267 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq1502
       have i₂ := eq10256
       grind)
    | exact superpose eq10256 eq1502
    | (have r₁ := eq1502
       have r₂ := eq10256
       grind)
    | exact resolve eq1502 eq10256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502 eq10256
  have eq10268 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq10267
  have eq10270 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10262 eq20
    | exact resolve eq20 eq10262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10262
  have eq11160 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10268 eq35
    | exact resolve eq35 eq10268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10268
  have eq11170 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq11160
    | exact resolve eq11160 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11160
  have eq11173 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10270 eq11170
    | exact resolve eq11170 eq10270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11170
  have eq11180 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11173 eq1545
    | exact resolve eq1545 eq11173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11191 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq11180
  have eq13932 : ∀ X0 X1 : G, (M.op x y) = (k (M.op X1 X1) (M.op (M.op (M.op X0 X0) (M.op x y)) x)) := by
    intro X0 X1
    first
    | exact superpose eq10266 eq752
    | exact resolve eq752 eq10266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq10266
  have eq14840 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11191 eq539
    | exact resolve eq539 eq11191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14865 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11191 eq925
    | exact resolve eq925 eq11191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11191
  have eq14929 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11173 eq14865
    | exact resolve eq14865 eq11173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11173 eq14865
  have eq14961 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq14840 eq14929
    | exact resolve eq14929 eq14840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14840 eq14929
  have eq14981 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq14961
    | exact resolve eq14961 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14961
  have eq14982 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14981
  have eq15016 : ∀ X0 : G, x = (M.op X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14982 eq539
    | exact resolve eq539 eq14982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq15081 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op (M.op X0 X0) (M.op x y)) x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14982 eq13932
    | exact resolve eq13932 eq14982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13932
  have eq15085 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 X0) (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14982 eq16
    | exact resolve eq16 eq14982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14982
  have eq15101 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15085 eq15081
    | exact resolve eq15081 eq15085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15081 eq15085
  have eq15515 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15101 eq35
    | exact resolve eq35 eq15101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq15101
  have eq15523 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15515
    | exact resolve eq15515 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15515
  have eq15528 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10270 eq15523
    | exact resolve eq15523 eq10270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15523
  have eq15588 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15528 eq1545
    | exact resolve eq1545 eq15528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq15602 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15588
  have eq15688 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq15602 eq925
    | exact resolve eq925 eq15602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq15723 : x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15602 eq15016
    | exact resolve eq15016 eq15602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15602
  have eq15733 : x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15723
  have eq15760 : (σ y) = (M.op x (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15016 eq15688
    | exact resolve eq15688 eq15016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15016 eq15688
  have eq15803 : (σ y) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15528 eq15760
    | exact resolve eq15760 eq15528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15528 eq15760
  have eq15838 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15733 eq15803
    | exact resolve eq15803 eq15733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15733 eq15803
  have eq15857 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15838
    | exact resolve eq15838 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15838
  have eq15858 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15857
  have eq15866 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq15858 eq27
    | exact resolve eq27 eq15858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15858
  have eq15873 : False := by grind
  exact eq15873

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_x_pxx_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
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
  have eq58 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq83 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq88 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq81
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq335 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq39
  have eq352 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq61 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq61 X2 X3 X0
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq64 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq61 X2 X3 X0
       grind)
    | exact superpose eq61 eq64
    | exact resolve eq64 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq665 : ∀ X0 X1 X3 : G, (M.op X1 X1) ≠ X0 ∨ (k X3 X0) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq65 X0 (M.op x (M.op (M.op X0 X0) (M.op X1 X1))) x
       have i₂ := eq61 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq61 eq65
    | (have r₁ := eq65 X0 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X1))) x
       have r₂ := eq61 (M.op X0 X0) X1 (M.op X0 X0)
       grind)
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq667 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X2 (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 (M.op X0 X0) X2
       have i₂ := eq352 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq65 X0 (M.op X0 X0) X2
       have i₂ := eq352 (M.op X0 X0) X1
       grind)
    | exact superpose eq352 eq65
    | (have r₁ := eq65 X1 (M.op X1 X1) X2
       have r₂ := eq352 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq65 X0 (M.op X0 X0) X2
       have r₂ := eq352 X0 (M.op X0 X0)
       grind)
    | exact resolve eq65 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq669 : ∀ X0 X2 : G, (k X2 (M.op X0 X0)) = X2 := by
    intro X0 X2
    first
    | (have j0 := eq667 X0 x X2
       grind)
    | (have r₁ := eq667 X0 x X2
       have r₂ := eq352 X0 x
       grind)
    | (have r₁ := eq667 x X0 X2
       have r₂ := eq352 X0 x
       grind)
    | exact resolve eq667 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq681 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 (M.op X1 X1)
       have i₂ := eq669 X1 (σ X0)
       grind)
    | exact superpose eq669 eq335
    | exact resolve eq335 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq682 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq681
    | exact resolve eq681 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq1442 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1 X1
       have i₂ := eq352 X0 (σ X1)
       grind)
    | (have i₁ := eq75 X1 X1
       have i₂ := eq352 (σ X1) X1
       grind)
    | exact superpose eq352 eq75
    | exact resolve eq75 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1476 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (M.op X2 X2) (σ X0)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) X2 (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq14
    | (have j1 := eq75 X0 X1
       grind)
    | exact resolve eq14 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1478 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1479 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq1513 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1442 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442
  have eq5302 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1479 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1479
    | (have j0 := eq1479 (τ X0)
       grind)
    | exact resolve eq1479 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1479
  have eq5320 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5302 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5302
    | (have j0 := eq5302 X0
       grind)
    | exact resolve eq5302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5302
  have eq5330 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5320 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5320
    | (have j0 := eq5320 X0
       grind)
    | exact resolve eq5320 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5320
  have eq7199 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq355 X1 x X2 x
       have i₂ := eq444 X1 x X2 x X0
       grind)
    | exact superpose eq444 eq355
    | exact resolve eq355 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq7772 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7199 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq355 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq355 eq7199
    | exact resolve eq7199 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq7199
  have eq8685 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7772 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7772
    | (have j0 := eq7772 x X0 y
       grind)
    | exact resolve eq7772 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7772
  have eq17794 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq88
       have i₂ := eq352 X0 x
       grind)
    | (have i₁ := eq88
       have i₂ := eq352 x x
       grind)
    | exact superpose eq352 eq88
    | exact resolve eq88 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq352
  have eq30303 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ x) (σ x))) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq16 (M.op X0 X0)
       have i₂ := eq17794 X0
       grind)
    | exact superpose eq17794 eq16
    | (have j1 := eq17794 X0
       grind)
    | exact resolve eq16 eq17794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17794
  have eq30388 : ∀ X0 : G, (M.op X0 X0) = (k x x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq50 eq30303
    | (have j0 := eq30303 X0
       grind)
    | exact resolve eq30303 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq30303
  have eq30815 : ∀ X0 : G, x ≠ (k x x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq30388 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30388
  have eq31078 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1513 X1 (M.op X0 X0)
       have i₂ := eq669 X0 (M.op X0 X0)
       grind)
    | exact superpose eq669 eq1513
    | (have j0 := eq1513 X1 (M.op X0 X0)
       grind)
    | exact resolve eq1513 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq1513
  have eq31461 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31078 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31078
  have eq31923 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq31461 X1 X0
       grind)
    | exact superpose eq31461 eq16
    | exact resolve eq16 eq31461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq46485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq46484
    | exact resolve eq46484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46484
  have eq46496 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq46485
       have r₂ := eq28
       grind)
    | exact resolve eq46485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46485
  have eq46559 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq46496 eq682
    | exact resolve eq682 eq46496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq46496
  have eq46694 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq46559
    | exact resolve eq46559 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46559
  have eq46701 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq46694 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq46694 X0
       have r₂ := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq46694 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq46694 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46694
  have eq46702 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq46701 X0
       have j1 := eq665 x x X0
       grind)
    | (have r₁ := eq46701 (M.op x x)
       have r₂ := eq665 (k (M.op x x) x) x x
       grind)
    | (have r₁ := eq46701 X0
       have r₂ := eq665 (σ x) (σ x) x
       grind)
    | (have r₁ := eq46701 X0
       have r₂ := eq665 x y x
       grind)
    | exact resolve eq46701 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46701
  have eq46820 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ x)) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31923 X0 X1
       have i₂ := eq46702 (M.op X0 X0)
       grind)
    | exact superpose eq46702 eq31923
    | (have j1 := eq46702 X1
       grind)
    | exact resolve eq31923 eq46702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46702
  have eq46887 : ∀ X0 X1 : G, (M.op X0 X0) = x ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29 eq46820
    | (have j0 := eq46820 X0 X1
       grind)
    | exact resolve eq46820 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq46820
  have eq46900 : ∀ X1 : G, (k X1 x) = X1 := by
    intro X1
    first
    | (have j0 := eq46887 x X1
       have j1 := eq665 x X1 X1
       grind)
    | (have r₁ := eq46887 X1 X1
       have r₂ := eq665 x X1 x
       grind)
    | (have r₁ := eq46887 x (M.op X1 X1)
       have r₂ := eq665 (k (M.op X1 X1) x) X1 x
       grind)
    | exact resolve eq46887 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq46887
  have eq46938 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq30815 X0
       have i₂ := eq46900 x
       grind)
    | exact superpose eq46900 eq30815
    | (have j0 := eq30815 X0
       grind)
    | (have r₁ := eq30815 X0
       have r₂ := eq46900 x
       grind)
    | exact resolve eq30815 eq46900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30815
  have eq46971 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5330 x
       have i₂ := eq46900 x
       grind)
    | exact superpose eq46900 eq5330
    | (have j0 := eq5330 x
       grind)
    | (have r₁ := eq5330 x
       have r₂ := eq46900 x
       grind)
    | exact resolve eq5330 eq46900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5330 eq46900
  have eq46997 : x = (M.op x x) := by grind
  clear eq46971
  have eq47004 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq46938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46938
  have eq47220 : y = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq8685 x
       have i₂ := eq46997
       grind)
    | exact superpose eq46997 eq8685
    | exact resolve eq8685 eq46997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8685
  have eq47304 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq47220
       have i₂ := eq46997
       grind)
    | exact superpose eq46997 eq47220
    | exact resolve eq47220 eq46997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47220
  have eq47489 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq31461 x X0
       have i₂ := eq47004 x
       grind)
    | exact superpose eq47004 eq31461
    | exact resolve eq31461 eq47004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31461
  have eq47498 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq31923 x X0
       have i₂ := eq47004 x
       grind)
    | exact superpose eq47004 eq31923
    | exact resolve eq31923 eq47004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31923
  have eq47787 : x = (τ x) := by
    first
    | (have i₁ := eq47498 x
       have i₂ := eq47004 x
       grind)
    | exact superpose eq47004 eq47498
    | exact resolve eq47498 eq47004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47498
  have eq47794 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq47489 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq47489
    | (have j0 := eq47489 X0
       grind)
    | exact resolve eq47489 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47489
  have eq47979 : x = (σ x) := by
    first
    | (have i₁ := eq47794 x
       have i₂ := eq47004 x
       grind)
    | exact superpose eq47004 eq47794
    | exact resolve eq47794 eq47004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47794
  have eq48061 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq47979 eq27
    | exact resolve eq27 eq47979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq48073 : (k x (M.op x y)) = (τ (k x (σ (M.op x y)))) := by
    first
    | exact superpose eq47979 eq58
    | exact resolve eq58 eq47979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq106890 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq47304 eq83
    | exact resolve eq83 eq47304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq106891 : (σ y) = (k x (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq47979 eq106890
    | exact resolve eq106890 eq47979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106890
  have eq106892 : (σ y) = (k x (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq106891
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq106891
    | exact resolve eq106891 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106891
  have eq106893 : x = (M.op x y) ∨ (σ y) = (k x (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq106892
       have i₂ := eq46997
       grind)
    | exact superpose eq46997 eq106892
    | exact resolve eq106892 eq46997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106892
  have eq106894 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (k x (σ (M.op x y))) := by
    first
    | (have i₁ := eq106893
       have i₂ := eq47004 sF0
       grind)
    | exact superpose eq47004 eq106893
    | exact resolve eq106893 eq47004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106893
  have eq106895 : (σ y) = (k x (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq106894
  have eq106897 : (τ (σ y)) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106895 eq48073
    | exact resolve eq48073 eq106895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48073 eq106895
  have eq106904 : y = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq106897
    | exact resolve eq106897 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq106897
  have eq106934 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106904 eq1476
    | (have j0 := eq1476 x (M.op x y) x
       grind)
    | exact resolve eq1476 eq106904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476 eq106904
  have eq106936 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq106934 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq106934
    | (have j0 := eq106934 X0
       grind)
    | exact resolve eq106934 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106934
  have eq106947 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq106936 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq106936
    | (have j0 := eq106936 X0
       grind)
    | exact resolve eq106936 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106936
  have eq106958 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq47979 eq106947
    | exact resolve eq106947 eq47979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106947
  have eq106962 : (σ (M.op x y)) = (M.op (M.op x x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106958 x
       have i₂ := eq47004 x
       grind)
    | exact superpose eq47004 eq106958
    | exact resolve eq106958 eq47004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106958
  have eq106965 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106962
       have i₂ := eq46997
       grind)
    | exact superpose eq46997 eq106962
    | exact resolve eq106962 eq46997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106962
  have eq106968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq48061 eq106965
    | exact resolve eq106965 eq48061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106965
  have eq106970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq106968
    | exact resolve eq106968 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106968
  have eq106972 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq106970
       have r₂ := eq28
       grind)
    | exact resolve eq106970 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106970
  have eq106974 : x = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106972
       have i₂ := eq47004 (σ x)
       grind)
    | exact superpose eq47004 eq106972
    | exact resolve eq106972 eq47004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106972
  have eq106976 : x = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq106974
    | exact resolve eq106974 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106974
  have eq106978 : x = (σ (M.op x y)) ∨ x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106976
       have i₂ := eq47004 (σ sF0)
       grind)
    | exact superpose eq47004 eq106976
    | exact resolve eq106976 eq47004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47004 eq106976
  have eq106980 : x = (σ (M.op x y)) ∨ x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq106978
    | exact resolve eq106978 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106978
  have eq106981 : x = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq106980
  have eq106984 : (M.op x y) = (τ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106981 eq31
    | exact resolve eq31 eq106981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq106981
  have eq107175 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106984
       have i₂ := eq47787
       grind)
    | exact superpose eq47787 eq106984
    | exact resolve eq106984 eq47787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47787 eq106984
  have eq107176 : x = (M.op x y) := by grind
  clear eq107175
  have eq107314 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq107176 eq21
    | exact resolve eq21 eq107176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq107413 : y = (M.op x x) := by
    first
    | exact superpose eq107176 eq47304
    | exact resolve eq47304 eq107176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47304 eq107176
  have eq107484 : x = y := by
    first
    | (have i₁ := eq107413
       have i₂ := eq46997
       grind)
    | exact superpose eq46997 eq107413
    | exact resolve eq107413 eq46997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107413
  have eq107572 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq107314
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq107314
    | exact resolve eq107314 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107314
  have eq107661 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq47979 eq107572
    | exact resolve eq107572 eq47979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107572
  have eq107808 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq107484
       grind)
    | exact superpose eq107484 eq25
    | exact resolve eq25 eq107484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq107484
  have eq108053 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq107808
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq107808
    | exact resolve eq107808 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq107808
  have eq108145 : x = (σ y) := by
    first
    | exact superpose eq47979 eq108053
    | exact resolve eq108053 eq47979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47979 eq108053
  have eq110168 : (M.op (σ x) (σ y)) = (M.op x x) := by
    first
    | exact superpose eq108145 eq48061
    | exact resolve eq48061 eq108145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48061 eq108145
  have eq110226 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110168
       have i₂ := eq46997
       grind)
    | exact superpose eq46997 eq110168
    | exact resolve eq110168 eq46997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46997 eq110168
  have eq110609 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq110226 eq28
    | exact resolve eq28 eq110226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq110226
  have eq110690 : False := by grind
  exact eq110690

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pxx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = X3 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = X3 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq35 X0 X1 X2 X3
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq104 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq20 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq146 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq397 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X2) ∨ (k X1 X2) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 X2 x (M.op X1 X2)
       have i₂ := eq104 X0 (M.op (M.op X1 X2) x)
       grind)
    | (have i₁ := eq57 X1 X2 x (M.op X1 X2)
       have i₂ := eq104 (M.op (M.op X1 X2) x) X0
       grind)
    | exact superpose eq104 eq57
    | (have j0 := eq57 X1 X2 X2 x
       grind)
    | exact resolve eq57 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq2222 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X2) ∨ (k X1 X2) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146 X1 X2
       have i₂ := eq104 X0 X1
       grind)
    | (have i₁ := eq146 X1 X2
       have i₂ := eq104 X1 X0
       grind)
    | exact superpose eq104 eq146
    | (have j0 := eq146 X1 X2
       grind)
    | (have r₁ := eq146 X0 X0
       have r₂ := eq104 X0 X0
       grind)
    | (have r₁ := eq146 X1 X1
       have r₂ := eq104 X1 X1
       grind)
    | exact resolve eq146 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq146
  have eq2240 : ∀ X1 X2 : G, (k X1 X2) = (M.op X1 X2) := by
    intro X1 X2
    first
    | (have j0 := eq2222 x X1 X2
       have j1 := eq397 x X1 X2
       grind)
    | (have r₁ := eq2222 x X1 X2
       have r₂ := eq397 x X1 X2
       grind)
    | (have r₁ := eq2222 X2 x x
       have r₂ := eq397 x X2 X2
       grind)
    | exact resolve eq2222 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq2222
  have eq140083 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2240 (σ X0) (σ X1)
       grind)
    | exact superpose eq2240 eq15
    | exact resolve eq15 eq2240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140102 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq140083 X0 X1
       have i₂ := eq2240 X0 X1
       grind)
    | exact superpose eq2240 eq140083
    | exact resolve eq140083 eq2240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2240 eq140083
  have eq140135 : False := by grind
  exact eq140135

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  clear eq43
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) := by
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
  clear eq44
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) := by
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
  have eq105 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
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
  have eq124 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq49
    | exact resolve eq49 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq127 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq124
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq124
    | exact resolve eq124 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq124
  have eq430 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq51 X2 X3 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq51 X2 X3 X0
       grind)
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq54
  have eq7049 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq430 X1 x X2 x
       have i₂ := eq509 X1 x X2 x X0
       grind)
    | exact superpose eq509 eq430
    | exact resolve eq430 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq7577 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7049 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq430 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq430 eq7049
    | exact resolve eq7049 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq7049
  have eq8451 : ∀ X0 : G, y = (M.op (M.op y x) (M.op y (M.op X0 X0))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7577 y X0 y
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq7577
    | exact resolve eq7577 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq8660 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq8451 x
       have i₂ := eq7577 y x x
       grind)
    | exact superpose eq7577 eq8451
    | exact resolve eq8451 eq7577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8451
  have eq9247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq8660 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq8660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq8660
  have eq9248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq9247
    | exact resolve eq9247 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9247
  have eq9251 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq9248
       have r₂ := eq27
       grind)
    | exact resolve eq9248 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9248
  have eq9324 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9251 eq7577
    | exact resolve eq7577 eq9251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9251
  have eq9326 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9324 x
       have i₂ := eq7577 sF3 x sF2
       grind)
    | exact superpose eq7577 eq9324
    | exact resolve eq9324 eq7577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7577 eq9324
  have eq9330 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq9326 eq29
    | exact resolve eq29 eq9326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9326
  have eq9358 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq9330
    | exact resolve eq9330 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9330
  have eq9359 : x = y := by grind
  clear eq9358
  have eq9365 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9359
       grind)
    | exact superpose eq9359 eq18
    | exact resolve eq18 eq9359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9366 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9359
       grind)
    | exact superpose eq9359 eq24
    | exact resolve eq24 eq9359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9359
  have eq9474 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq9366
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9366
    | exact resolve eq9366 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9366
  have eq9503 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9474 eq26
    | exact resolve eq26 eq9474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9474
  have eq9647 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq9503 eq127
    | exact resolve eq127 eq9503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq9503
  have eq9729 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq9647
       have i₂ := eq9365
       grind)
    | exact superpose eq9365 eq9647
    | exact resolve eq9647 eq9365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9365 eq9647
  have eq9734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9729 eq15
    | exact resolve eq15 eq9729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9729
  have eq9774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9734
    | exact resolve eq9734 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9734
  have eq9783 : False := by grind
  exact eq9783

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq14 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X0) (σ X1)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq59 (τ X0) X1
       grind)
    | exact superpose eq59 eq18
    | (have j1 := eq59 (τ X0) X1
       grind)
    | exact resolve eq18 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq242 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X0 (M.op X0 X0) X2
       have i₂ := eq82 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq35 X0 (M.op X0 X0) X2
       have i₂ := eq82 (M.op X0 X0) X1
       grind)
    | exact superpose eq82 eq35
    | (have r₁ := eq35 X1 (M.op X1 X1) X2
       have r₂ := eq82 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq35 X0 (M.op X0 X0) X2
       have r₂ := eq82 X0 (M.op X0 X0)
       grind)
    | exact resolve eq35 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 X3 : G, (M.op X1 X1) ≠ X0 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq35 X0 (M.op x (M.op (M.op X0 X0) (M.op X1 X1))) x
       have i₂ := eq25 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq25 eq35
    | (have r₁ := eq35 X0 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X1))) x
       have r₂ := eq25 (M.op X0 X0) X1 (M.op X0 X0)
       grind)
    | exact resolve eq35 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq35
  have eq247 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq242 X0 x X2
       grind)
    | (have r₁ := eq242 X0 x X2
       have r₂ := eq82 X0 x
       grind)
    | (have r₁ := eq242 x X0 X2
       have r₂ := eq82 X0 x
       grind)
    | exact resolve eq242 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq312 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (τ X0)
       have i₂ := eq82 X0 (τ X0)
       grind)
    | (have i₁ := eq76 X0 (τ X0)
       have i₂ := eq82 (τ X0) X1
       grind)
    | exact superpose eq82 eq76
    | (have j0 := eq76 X1 X0
       grind)
    | exact resolve eq76 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq332 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq312
    | (have j0 := eq312 X0 X1
       grind)
    | exact resolve eq312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq361 : ∀ X0 X1 : G, (M.op X1 X1) = (τ X0) ∨ (M.op X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq332 X1 X0
       grind)
    | exact superpose eq332 eq10
    | (have j1 := eq332 X1 X0
       grind)
    | exact resolve eq10 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq177
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq177
    | (have j1 := eq59 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq177
  have eq503 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq502
  have eq792 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq503
       have i₂ := eq82 X0 y
       grind)
    | (have i₁ := eq503
       have i₂ := eq82 y X0
       grind)
    | exact superpose eq82 eq503
    | exact resolve eq503 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq3129 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq361 X1 X0
       grind)
    | exact superpose eq361 eq11
    | (have j1 := eq361 (k X1 X1) X0
       grind)
    | exact resolve eq11 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq7059 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X1)
       have i₂ := eq3129 X0 X1
       grind)
    | exact superpose eq3129 eq11
    | (have j1 := eq3129 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq3129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129
  have eq12323 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7059 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7059
  have eq26446 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12323 X1 (M.op X0 X0)
       have i₂ := eq247 X0 (M.op X0 X0)
       grind)
    | exact superpose eq247 eq12323
    | (have j0 := eq12323 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12323 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12323
  have eq26488 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26446 X0 X1
       grind)
    | (have r₁ := eq26446 X1 X1
       have r₂ := eq82 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq26446 X0 X1
       have r₂ := eq82 X0 (M.op X0 X0)
       grind)
    | exact resolve eq26446 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq26446
  have eq26928 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq26488 X0 X1
       grind)
    | exact superpose eq26488 eq10
    | exact resolve eq10 eq26488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27243 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ x)) ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq26928 (σ y) X0
       have i₂ := eq792 X1
       grind)
    | exact superpose eq792 eq26928
    | (have j1 := eq792 X1
       grind)
    | exact resolve eq26928 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq26928
  have eq27673 : ∀ X0 X1 : G, x = (M.op X0 X0) ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq27243 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27243
    | (have j0 := eq27243 X0 X0
       grind)
    | exact resolve eq27243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27243
  have eq30236 : ∀ X0 X2 : G, (M.op X0 x) = (k X0 x) ∨ x = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq247 X0 X2
       have i₂ := eq27673 X0 x
       grind)
    | exact superpose eq27673 eq247
    | (have j1 := eq27673 X2 X2
       grind)
    | exact resolve eq247 eq27673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq30426 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq27673 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27673
  have eq30427 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq30426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30426
  have eq30491 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq30236 X0 x
       have j1 := eq246 x x X0
       grind)
    | (have r₁ := eq30236 x x
       have r₂ := eq246 (k x x) x x
       grind)
    | (have r₁ := eq30236 X0 x
       have r₂ := eq246 x x x
       grind)
    | exact resolve eq30236 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq30236
  have eq30702 : ∀ X1 : G, x = (σ (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq26488 x X1
       have i₂ := eq30427 x
       grind)
    | exact superpose eq30427 eq26488
    | exact resolve eq26488 eq30427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26488
  have eq30715 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X1
       have i₂ := eq30427 X1
       grind)
    | exact superpose eq30427 eq9
    | exact resolve eq9 eq30427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30809 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq30427 (M.op X0 X0)
       grind)
    | exact superpose eq30427 eq9
    | exact resolve eq9 eq30427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30886 : ∀ X1 : G, (M.op x (M.op X1 x)) = X1 := by
    intro X1
    first
    | (have i₁ := eq30809 x X1
       have i₂ := eq30427 x
       grind)
    | exact superpose eq30427 eq30809
    | exact resolve eq30809 eq30427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30809
  have eq30965 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 := by
    intro X1
    first
    | (have i₁ := eq30715 x X1
       have i₂ := eq30427 x
       grind)
    | exact superpose eq30427 eq30715
    | exact resolve eq30715 eq30427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30715
  have eq30974 : x = (σ x) := by
    first
    | (have i₁ := eq30702 x
       have i₂ := eq30427 x
       grind)
    | exact superpose eq30427 eq30702
    | exact resolve eq30702 eq30427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30427 eq30702
  have eq31302 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30974
       grind)
    | exact superpose eq30974 eq16
    | exact resolve eq16 eq30974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31411 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq30491 (τ X0)
       grind)
    | exact superpose eq30491 eq18
    | exact resolve eq18 eq30491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31437 : ∀ X0 : G, (k X0 x) = (σ (M.op (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq31411 X0
       have i₂ := eq30974
       grind)
    | exact superpose eq30974 eq31411
    | exact resolve eq31411 eq30974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30974 eq31411
  have eq31468 : ∀ X0 : G, (M.op X0 x) = (σ (M.op (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq31437 X0
       have i₂ := eq30491 X0
       grind)
    | exact superpose eq30491 eq31437
    | exact resolve eq31437 eq30491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30491 eq31437
  have eq35857 : ∀ X0 : G, (σ (M.op X0 x)) = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq31468 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31468
    | exact resolve eq31468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31468
  have eq38068 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq35857 (M.op x X0)
       have i₂ := eq30965 X0
       grind)
    | exact superpose eq30965 eq35857
    | exact resolve eq35857 eq30965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30965 eq35857
  have eq39574 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq30886 (σ (M.op x X0))
       have i₂ := eq38068 X0
       grind)
    | exact superpose eq38068 eq30886
    | exact resolve eq30886 eq38068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30886 eq38068
  have eq40947 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq31302
       have i₂ := eq39574 y
       grind)
    | exact superpose eq39574 eq31302
    | (have r₁ := eq31302
       have r₂ := eq39574 y
       grind)
    | exact resolve eq31302 eq39574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31302 eq39574
  have eq41009 : False := by grind
  exact eq41009

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq99 (σ X0) (σ X1)
       grind)
    | exact superpose eq99 eq15
    | (have j1 := eq99 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq108
    | (have j0 := eq108 X0 X1
       have j1 := eq99 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq108 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq108
  have eq315 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq94 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq94 (σ X1) X0
       grind)
    | exact superpose eq94 eq22
    | exact resolve eq22 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq94
  have eq2044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq144 x y
       grind)
    | exact superpose eq144 eq16
    | (have j1 := eq144 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq144 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq144 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq144 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq2057 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2044
  have eq7787 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2057
       grind)
    | exact superpose eq2057 eq10
    | exact resolve eq10 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq7800 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7787
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7787
    | exact resolve eq7787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7787
  have eq7801 : x = y := by grind
  clear eq7800
  have eq17798 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7801
       grind)
    | exact superpose eq7801 eq16
    | exact resolve eq16 eq7801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7801
  have eq17799 : False := by grind
  exact eq17799
