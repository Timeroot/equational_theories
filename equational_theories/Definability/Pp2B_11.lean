import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq9 (M.op X0 X0) X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq31
    | exact resolve eq31 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq56 X0 (τ X1)
       grind)
    | exact superpose eq56 eq18
    | (have j1 := eq56 X0 (τ X1)
       grind)
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq56
  have eq84 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 X0) X1 x
       have i₂ := eq9 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq67
    | exact resolve eq67 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq67
  have eq156 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | (have r₁ := eq34 x X1
       have r₂ := eq24 x x x
       grind)
    | (have r₁ := eq34 (M.op x x) X1
       have r₂ := eq24 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq34 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq163 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq156 (M.op X1 X1) X1
       have i₂ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq156
    | exact resolve eq156 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq280 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k (σ (τ X1)) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (τ X1) X1
       have i₂ := eq84 X0 (τ X1)
       grind)
    | (have i₁ := eq73 (τ X1) X1
       have i₂ := eq84 (τ X1) X1
       grind)
    | exact superpose eq84 eq73
    | exact resolve eq73 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq84
  have eq305 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq339 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq305 X0 X1
       grind)
    | exact superpose eq305 eq11
    | (have j1 := eq305 X0 X1
       grind)
    | exact resolve eq11 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq499 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op X1 X1)
       have i₂ := eq163 X1 (σ X0)
       grind)
    | exact superpose eq163 eq31
    | exact resolve eq31 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq616 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq132 X0 X1 X2
       grind)
    | exact superpose eq132 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq132 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq132 X0 X1 X2
       grind)
    | exact resolve eq13 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq616 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq618 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq617 X0 X1 X2
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq617
    | (have j0 := eq617 X0 X1 X2
       grind)
    | exact resolve eq617 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq617
  have eq2229 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq339 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq2283 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2229 X1 (M.op X0 X0)
       have i₂ := eq163 X0 (M.op X0 X0)
       grind)
    | exact superpose eq163 eq2229
    | (have j0 := eq2229 X1 (M.op X0 X0)
       grind)
    | exact resolve eq2229 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229
  have eq2289 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2283 X0 X1
       grind)
    | (have r₁ := eq2283 x X1
       have r₂ := eq24 x x x
       grind)
    | (have r₁ := eq2283 (M.op x x) X1
       have r₂ := eq24 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq2283 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2283
  have eq2410 : ∀ X0 X1 X2 : G, (k (τ X1) (M.op X2 X2)) = (τ (k X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 (M.op X2 X2)
       have i₂ := eq2289 X0 X2
       grind)
    | exact superpose eq2289 eq22
    | exact resolve eq22 eq2289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2289
  have eq2437 : ∀ X0 X1 X2 : G, (k (τ X1) (M.op X2 X2)) = (τ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2410 X0 X1 X2
       have i₂ := eq163 X0 X1
       grind)
    | exact superpose eq163 eq2410
    | exact resolve eq2410 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410
  have eq2453 : ∀ X0 X1 X2 : G, (M.op (τ X1) (M.op X2 X2)) = (τ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2437 X0 X1 X2
       have i₂ := eq163 X2 (τ X1)
       grind)
    | exact superpose eq163 eq2437
    | exact resolve eq2437 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq2437
  have eq41490 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq618 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq41494 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41490 X0 X1 X2
       have j1 := eq132 X0 X1 X2
       grind)
    | (have r₁ := eq41490 X0 X1 X2
       have r₂ := eq132 X0 X1 X2
       grind)
    | exact resolve eq41490 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq41490
  have eq100511 : ∀ X0 X1 X2 : G, (M.op (τ (σ X0)) (M.op X1 X1)) = (k X0 (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq499 X0 X2
       have i₂ := eq2453 X2 (σ X0) X1
       grind)
    | exact superpose eq2453 eq499
    | exact resolve eq499 eq2453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq2453
  have eq100670 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k X0 (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100511 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100511
    | exact resolve eq100511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100511
  have eq100929 : ∀ X0 X1 X3 : G, (k (M.op (M.op X1 X1) X0) (τ (M.op X3 X3))) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq100670 (M.op (M.op X1 X1) X0) x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq100670
    | exact resolve eq100670 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100670
  have eq710472 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ (τ X1))) (σ (τ X2))) = (σ (τ (k (k (σ (τ X0)) X1) X2))) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41494 X0 (τ X1) (τ X2)
       have i₂ := eq46 (τ X0) X1 X2
       grind)
    | exact superpose eq46 eq41494
    | (have j0 := eq41494 X0 X1 (τ X2)
       grind)
    | exact resolve eq41494 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq41494
  have eq711465 : ∀ X0 X1 X2 : G, (k (k (σ (τ X0)) X1) X2) = (M.op (k X0 (σ (τ X1))) (σ (τ X2))) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq710472 X0 X1 X2
       have i₂ := eq11 (k (k (σ (τ X0)) X1) X2)
       grind)
    | exact superpose eq11 eq710472
    | (have j0 := eq710472 X0 X1 X2
       grind)
    | exact resolve eq710472 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710472
  have eq711766 : ∀ X0 X1 X2 : G, (k (k (σ (τ X0)) X1) X2) = (M.op (k X0 (σ (τ X1))) X2) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq711465 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq711465
    | (have j0 := eq711465 X0 X1 X2
       grind)
    | exact resolve eq711465 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711465
  have eq711888 : ∀ X0 X1 X2 : G, (k (k (σ (τ X0)) X1) X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq711766 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq711766
    | (have j0 := eq711766 X0 X1 X2
       grind)
    | exact resolve eq711766 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711766
  have eq711945 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq711888 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq711888
    | (have j0 := eq711888 X0 X1 X2
       grind)
    | exact resolve eq711888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711888
  have eq711969 : ∀ X0 X1 X2 : G, (M.op X2 X2) = X2 ∨ (k (k X0 X1) X2) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq711945 X0 X1 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq711945
    | (have j0 := eq711945 X0 X1 X2
       grind)
    | exact resolve eq711945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711945
  have eq711977 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq711969 X0 X1 X2
       have j1 := eq12 (k X0 X1) X2
       grind)
    | (have r₁ := eq711969 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq711969 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711969
  have eq712118 : ∀ X0 X3 : G, (k X0 X3) = (M.op X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq711977 (M.op (M.op x x) X0) (τ (M.op X3 X3)) x
       have i₂ := eq100929 X0 x X3
       grind)
    | exact superpose eq100929 eq711977
    | exact resolve eq711977 eq100929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100929 eq711977
  have eq713359 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq712118 (σ X0) (σ X1)
       grind)
    | exact superpose eq712118 eq15
    | exact resolve eq15 eq712118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713552 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq713359 X0 X1
       have i₂ := eq712118 X0 X1
       grind)
    | exact superpose eq712118 eq713359
    | exact resolve eq713359 eq712118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712118 eq713359
  have eq719042 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq713552 x y
       grind)
    | exact superpose eq713552 eq16
    | (have r₁ := eq16
       have r₂ := eq713552 x y
       grind)
    | exact resolve eq16 eq713552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713552
  have eq719980 : False := by grind
  exact eq719980

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq9 (M.op X0 X0) X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq56 (τ X0) X1
       grind)
    | exact superpose eq56 eq17
    | (have j1 := eq56 (τ X0) X1
       grind)
    | exact resolve eq17 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 X0) X1 x
       have i₂ := eq9 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq67
    | exact resolve eq67 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq67
  have eq156 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | (have r₁ := eq34 x X1
       have r₂ := eq24 x x x
       grind)
    | (have r₁ := eq34 (M.op x x) X1
       have r₂ := eq24 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq34 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq163 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq156 (M.op X1 X1) X1
       have i₂ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq156
    | exact resolve eq156 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq280 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k X1 (σ (τ X1))) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (τ X0)
       have i₂ := eq84 X0 (τ X0)
       grind)
    | (have i₁ := eq71 X0 (τ X0)
       have i₂ := eq84 (τ X0) X1
       grind)
    | exact superpose eq84 eq71
    | exact resolve eq71 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq84
  have eq304 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq338 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq304 X0 X1
       grind)
    | exact superpose eq304 eq11
    | (have j1 := eq304 X0 X1
       grind)
    | exact resolve eq11 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq499 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op X1 X1)
       have i₂ := eq163 X1 (σ X0)
       grind)
    | exact superpose eq163 eq31
    | exact resolve eq31 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq616 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq135 X0 X1 X2
       grind)
    | exact superpose eq135 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq135 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq135 X0 X1 X2
       grind)
    | exact resolve eq13 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq617 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq616 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq618 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k X2 (k (τ X0) X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq617 X0 X1 X2
       have i₂ := eq20 X0 X1 X2
       grind)
    | exact superpose eq20 eq617
    | (have j0 := eq617 X0 X1 X2
       grind)
    | exact resolve eq617 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq617
  have eq2228 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq338 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq2282 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2228 X1 (M.op X0 X0)
       have i₂ := eq163 X0 (M.op X0 X0)
       grind)
    | exact superpose eq163 eq2228
    | (have j0 := eq2228 X1 (M.op X0 X0)
       grind)
    | exact resolve eq2228 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq2288 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2282 X0 X1
       grind)
    | (have r₁ := eq2282 x X1
       have r₂ := eq24 x x x
       grind)
    | (have r₁ := eq2282 (M.op x x) X1
       have r₂ := eq24 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq2282 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2282
  have eq2409 : ∀ X0 X1 X2 : G, (k (τ X1) (M.op X2 X2)) = (τ (k X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 (M.op X2 X2)
       have i₂ := eq2288 X0 X2
       grind)
    | exact superpose eq2288 eq22
    | exact resolve eq22 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2288
  have eq2436 : ∀ X0 X1 X2 : G, (k (τ X1) (M.op X2 X2)) = (τ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2409 X0 X1 X2
       have i₂ := eq163 X0 X1
       grind)
    | exact superpose eq163 eq2409
    | exact resolve eq2409 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2452 : ∀ X0 X1 X2 : G, (M.op (τ X1) (M.op X2 X2)) = (τ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2436 X0 X1 X2
       have i₂ := eq163 X2 (τ X1)
       grind)
    | exact superpose eq163 eq2436
    | exact resolve eq2436 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq2436
  have eq56711 : ∀ X0 X1 X2 : G, (k X1 (σ (τ X2))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) ∨ (k X1 (σ (τ X2))) = (M.op (k X1 (σ (τ X2))) (k X1 (σ (τ X2)))) ∨ (M.op (σ (τ X0)) (k X1 (σ (τ X2)))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq618 X0 (τ X1) (τ X2)
       have i₂ := eq37 (τ X0) X1 X2
       grind)
    | exact superpose eq37 eq618
    | (have j0 := eq618 X1 (τ X2) X2
       grind)
    | exact resolve eq618 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq618
  have eq56945 : ∀ X0 X1 X2 : G, (k X1 (σ (τ X2))) = (k X0 (k (σ (τ X1)) X2)) ∨ (k X1 (σ (τ X2))) = (M.op (k X1 (σ (τ X2))) (k X1 (σ (τ X2)))) ∨ (M.op (σ (τ X0)) (k X1 (σ (τ X2)))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56711 X0 X1 X2
       have i₂ := eq11 (k X0 (k (σ (τ X1)) X2))
       grind)
    | exact superpose eq11 eq56711
    | (have j0 := eq56711 X0 X1 X2
       grind)
    | exact resolve eq56711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56711
  have eq57042 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X1 (σ (τ X2))) ∨ (k X1 (σ (τ X2))) = (M.op (k X1 (σ (τ X2))) (k X1 (σ (τ X2)))) ∨ (M.op (σ (τ X0)) (k X1 (σ (τ X2)))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56945 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq56945
    | (have j0 := eq56945 X0 X1 X2
       grind)
    | exact resolve eq56945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56945
  have eq57119 : ∀ X0 X1 X2 : G, (k X1 X2) = (k X0 (k X1 X2)) ∨ (k X1 (σ (τ X2))) = (M.op (k X1 (σ (τ X2))) (k X1 (σ (τ X2)))) ∨ (M.op (σ (τ X0)) (k X1 (σ (τ X2)))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57042 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq57042
    | (have j0 := eq57042 X0 X1 X2
       grind)
    | exact resolve eq57042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57042
  have eq57186 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op (k X1 X2) (k X1 X2)) ∨ (k X1 X2) = (k X0 (k X1 X2)) ∨ (M.op (σ (τ X0)) (k X1 (σ (τ X2)))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57119 X0 X1 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57119
    | (have j0 := eq57119 X0 X1 X2
       grind)
    | exact resolve eq57119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57119
  have eq57225 : ∀ X0 X1 X2 : G, (k X0 (k (σ (τ X1)) X2)) = (M.op (σ (τ X0)) (k X1 (σ (τ X2)))) ∨ (k X1 X2) = (M.op (k X1 X2) (k X1 X2)) ∨ (k X1 X2) = (k X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57186 X0 X1 X2
       have i₂ := eq11 (k X0 (k (σ (τ X1)) X2))
       grind)
    | exact superpose eq11 eq57186
    | (have j0 := eq57186 X0 X1 X2
       grind)
    | exact resolve eq57186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57186
  have eq57251 : ∀ X0 X1 X2 : G, (k X0 (k (σ (τ X1)) X2)) = (M.op (σ (τ X0)) (k X1 X2)) ∨ (k X1 X2) = (M.op (k X1 X2) (k X1 X2)) ∨ (k X1 X2) = (k X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57225 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq57225
    | (have j0 := eq57225 X0 X1 X2
       grind)
    | exact resolve eq57225 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57225
  have eq57274 : ∀ X0 X1 X2 : G, (k X0 (k (σ (τ X1)) X2)) = (M.op X0 (k X1 X2)) ∨ (k X1 X2) = (M.op (k X1 X2) (k X1 X2)) ∨ (k X1 X2) = (k X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57251 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57251
    | (have j0 := eq57251 X0 X1 X2
       grind)
    | exact resolve eq57251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57251
  have eq57284 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) ∨ (k X1 X2) = (M.op (k X1 X2) (k X1 X2)) ∨ (k X1 X2) = (k X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57274 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq57274
    | (have j0 := eq57274 X0 X1 X2
       grind)
    | exact resolve eq57274 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57274
  have eq57288 : ∀ X0 X1 X2 : G, (k X1 X2) = (k X0 (k X1 X2)) ∨ (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq57284 X0 X1 X2
       have j1 := eq12 X0 (k X1 X2)
       grind)
    | (have r₁ := eq57284 X0 X1 X2
       have r₂ := eq12 X0 (k X1 X2)
       grind)
    | exact resolve eq57284 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57284
  have eq107283 : ∀ X0 X1 X2 : G, (M.op (τ (σ X0)) (M.op X1 X1)) = (k X0 (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq499 X0 X2
       have i₂ := eq2452 X2 (σ X0) X1
       grind)
    | exact superpose eq2452 eq499
    | exact resolve eq499 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq2452
  have eq107444 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k X0 (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107283 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq107283
    | exact resolve eq107283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107283
  have eq107700 : ∀ X0 X1 X3 : G, (k (M.op (M.op X1 X1) X0) (τ (M.op X3 X3))) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq107444 (M.op (M.op X1 X1) X0) x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq107444
    | exact resolve eq107444 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107444
  have eq491053 : ∀ X0 X1 X2 : G, (k X1 X2) ≠ (M.op X0 (k X1 X2)) ∨ (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq57288 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57288
  have eq491096 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq491053 X0 X1 X2
       have j1 := eq56 X0 (k X1 X2)
       grind)
    | (have r₁ := eq491053 X0 X1 X2
       have r₂ := eq56 X0 (k X1 X2)
       grind)
    | exact resolve eq491053 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq491053
  have eq586712 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq491096 X0 (M.op (M.op X1 X1) X0) (τ (M.op x x))
       have i₂ := eq107700 X0 X1 x
       grind)
    | exact superpose eq107700 eq491096
    | exact resolve eq491096 eq107700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107700 eq491096
  have eq587888 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq586712 (σ X1) (σ X0)
       grind)
    | exact superpose eq586712 eq15
    | exact resolve eq15 eq586712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588069 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq587888 X0 X1
       have i₂ := eq586712 X1 X0
       grind)
    | exact superpose eq586712 eq587888
    | exact resolve eq587888 eq586712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586712 eq587888
  have eq593429 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq588069 x y
       grind)
    | exact superpose eq588069 eq16
    | (have r₁ := eq16
       have r₂ := eq588069 x y
       grind)
    | exact resolve eq16 eq588069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588069
  have eq594284 : False := by grind
  exact eq594284

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq50 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 X2) (M.op X3 X3)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X0 X3
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq20 X0 X0 X2
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 X2) (M.op X3 X3)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq93 X0 X1 X2 X3
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq93 (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X2 X2) (M.op X3 X3)) X2 X3
       have r₂ := eq12 X0 (M.op (M.op X2 X2) (M.op X3 X3))
       grind)
    | (have r₁ := eq93 X1 X1 X1 X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq93 X1 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq168 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1250 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq168 X3 X2
       have i₂ := eq20 X0 X3 X1
       grind)
    | (have i₁ := eq168 (M.op X2 X2) X1
       have i₂ := eq20 X2 X1 X2
       grind)
    | exact superpose eq20 eq168
    | (have j0 := eq168 X3 X2
       grind)
    | (have r₁ := eq168 (M.op X2 X2) (M.op X2 X2)
       have r₂ := eq20 X2 (M.op X2 X2) X2
       grind)
    | (have r₁ := eq168 (M.op X2 X2) (M.op X0 X0)
       have r₂ := eq20 X0 (M.op X2 X2) X2
       grind)
    | exact resolve eq168 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq168
  have eq1266 : ∀ X2 X3 : G, (M.op X2 X3) = (k X3 X2) := by
    intro X2 X3
    first
    | (have j0 := eq1250 x x X2 X3
       have j1 := eq132 X2 X3 X2 X3
       grind)
    | (have r₁ := eq1250 X2 X3 x x
       have r₂ := eq132 x x X2 X3
       grind)
    | (have r₁ := eq1250 x x (M.op X2 X2) (M.op X3 X3)
       have r₂ := eq132 (M.op x x) (M.op x x) X2 X3
       grind)
    | exact resolve eq1250 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq1250
  have eq15953 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1266 (σ X0) (σ X1)
       grind)
    | exact superpose eq1266 eq15
    | exact resolve eq15 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15968 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15953 X0 X1
       have i₂ := eq1266 X0 X1
       grind)
    | exact superpose eq1266 eq15953
    | exact resolve eq15953 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq15953
  have eq15985 : False := by grind
  exact eq15985

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq44 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq58
    | exact resolve eq58 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq58
  have eq81 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq81
    | (have j0 := eq81 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq81 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq309 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq150
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq150
    | (have j1 := eq81 (σ x) (σ y)
       grind)
    | (have r₁ := eq150
       have r₂ := eq81 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq150
       have r₂ := eq81 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq150 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq150
  have eq310 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq309
  have eq311 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq310
       grind)
    | exact superpose eq310 eq16
    | exact resolve eq16 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq312 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq311
       have r₂ := eq67 x
       grind)
    | exact resolve eq311 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq314 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq312
       grind)
    | exact superpose eq312 eq10
    | exact resolve eq10 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq327 : x = y := by
    first
    | (have i₁ := eq314
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq314
    | exact resolve eq314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq329 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq327
       grind)
    | exact superpose eq327 eq16
    | exact resolve eq16 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq330 : False := by grind
  exact eq330

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq44 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq58
    | exact resolve eq58 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq58
  have eq81 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq81
    | (have j0 := eq81 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq81 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 y x
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq309 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq150
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq150
    | (have j1 := eq81 (σ x) (σ y)
       grind)
    | (have r₁ := eq150
       have r₂ := eq81 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq150
       have r₂ := eq81 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq150 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq150
  have eq310 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq309
  have eq311 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq310
       grind)
    | exact superpose eq310 eq16
    | exact resolve eq16 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq312 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq311
       have r₂ := eq67 x
       grind)
    | exact resolve eq311 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq314 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq312
       grind)
    | exact superpose eq312 eq10
    | exact resolve eq10 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq327 : x = y := by
    first
    | (have i₁ := eq314
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq314
    | exact resolve eq314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq329 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq327
       grind)
    | exact superpose eq327 eq16
    | exact resolve eq16 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq330 : False := by grind
  exact eq330

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pyy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq364 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq391 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq307
    | exact resolve eq307 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq538 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
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
  have eq558 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X1 X0
       grind)
    | exact superpose eq538 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq538 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq538 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq538 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq538 X2 X0
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq538 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq538 (M.op X1 X1) X0
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq558 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (k X0 (M.op X1 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq567 X2 X1 X0
       have i₂ := eq929 X0 X1
       grind)
    | exact superpose eq929 eq567
    | exact resolve eq567 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (k X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X0 X1 X2
       have i₂ := eq929 X0 X1
       grind)
    | exact superpose eq929 eq175
    | exact resolve eq175 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq982 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X1) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq563 X2 X0 X1
       have i₂ := eq929 (M.op (M.op X0 X0) X1) X2
       grind)
    | exact superpose eq929 eq563
    | exact resolve eq563 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq929
  have eq1554 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1555 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1596 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq538 X0 X1
       grind)
    | exact superpose eq538 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq538 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq538 X1 X1
       grind)
    | exact resolve eq12 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1621 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1622 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1596 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1626 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1621 X0
       have j1 := eq558 X0 X0 X0
       grind)
    | (have r₁ := eq1621 x
       have r₂ := eq558 x x x
       grind)
    | (have r₁ := eq1621 (M.op X0 X0)
       have r₂ := eq558 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | (have r₁ := eq1621 X0
       have r₂ := eq558 X0 (k X0 X0) x
       grind)
    | exact resolve eq1621 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq1621
  have eq1704 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq1626 X0
       grind)
    | exact superpose eq1626 eq538
    | exact resolve eq538 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq1719 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (k X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq954 X1 X2 X0
       have i₂ := eq1626 X0
       grind)
    | exact superpose eq1626 eq954
    | exact resolve eq954 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1722 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (k X1 (k X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq957 X1 X0 X2
       have i₂ := eq1626 X0
       grind)
    | exact superpose eq1626 eq957
    | exact resolve eq957 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1727 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq982 X1 X2 X0
       have i₂ := eq1626 X0
       grind)
    | exact superpose eq1626 eq982
    | exact resolve eq982 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq1738 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X0 X1
       have i₂ := eq1626 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1626 eq16
    | exact resolve eq16 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1751 : ∀ X0 X1 : G, (k X0 X0) = (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1738 X0 X1
       have i₂ := eq1626 X0
       grind)
    | exact superpose eq1626 eq1738
    | exact resolve eq1738 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq1757 : ∀ X0 X1 X2 : G, (k (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1727 X0 X1 X2
       have i₂ := eq1626 X1
       grind)
    | exact superpose eq1626 eq1727
    | exact resolve eq1727 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1764 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (k X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1719 X0 X1 X2
       have i₂ := eq1626 X2
       grind)
    | exact superpose eq1626 eq1719
    | exact resolve eq1719 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq1894 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1704 (σ X1) X0
       grind)
    | exact superpose eq1704 eq10
    | exact resolve eq10 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1895 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X1 (σ X1)
       have i₂ := eq1704 (σ X1) X0
       grind)
    | exact superpose eq1704 eq364
    | exact resolve eq364 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq1896 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq391 X1 X1
       have i₂ := eq1704 (τ X1) X0
       grind)
    | exact superpose eq1704 eq391
    | exact resolve eq391 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704
  have eq1900 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1895 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq1895
    | exact resolve eq1895 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895
  have eq1949 : ∀ X0 X1 : G, (k X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1900 X0 X1
       have i₂ := eq1626 X0
       grind)
    | exact superpose eq1626 eq1900
    | exact resolve eq1900 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq2195 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (k X1 (σ (k X0 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq957 X1 x X2
       have i₂ := eq1894 x X0
       grind)
    | exact superpose eq1894 eq957
    | exact resolve eq957 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq2379 : ∀ X0 X2 : G, (τ (k X0 X0)) = (τ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1896 x X2
       have i₂ := eq1896 x X0
       grind)
    | exact superpose eq1896 eq1896
    | exact resolve eq1896 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2395 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1896 X1 (τ X0)
       have i₂ := eq391 X0 X0
       grind)
    | exact superpose eq391 eq1896
    | exact resolve eq1896 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2443 : ∀ X0 X2 : G, (τ (k X0 X0)) = (σ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1894 x X2
       have i₂ := eq1896 x X0
       grind)
    | exact superpose eq1896 eq1894
    | exact resolve eq1894 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894 eq1896
  have eq2743 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1949 (τ X0) X1
       have i₂ := eq391 X0 X0
       grind)
    | exact superpose eq391 eq1949
    | exact resolve eq1949 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3457 : ∀ X0 X2 : G, (τ (τ (k X0 X0))) = (τ (τ (k X2 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq2395 X2 x
       have i₂ := eq2395 X0 x
       grind)
    | exact superpose eq2395 eq2395
    | exact resolve eq2395 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395
  have eq3993 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1949 x X1
       have i₂ := eq2743 X0 x
       grind)
    | exact superpose eq2743 eq1949
    | exact resolve eq1949 eq2743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq3998 : ∀ X0 X2 : G, (τ (k X2 X2)) = (τ (τ (τ (k X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq2379 x X2
       have i₂ := eq2743 X0 x
       grind)
    | exact superpose eq2743 eq2379
    | exact resolve eq2379 eq2743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379
  have eq5636 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (τ (τ (τ (k X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2743 x X1
       have i₂ := eq3993 X0 x
       grind)
    | exact superpose eq3993 eq2743
    | exact resolve eq2743 eq3993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3993
  have eq6174 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 X3))) X1) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq178 X2 x X3 X4
       have i₂ := eq178 X1 X0 (M.op X2 X3) x
       grind)
    | (have i₁ := eq178 X0 (M.op (M.op X0 X2) (M.op X0 X2)) X2 X3
       have i₂ := eq178 (M.op X0 X2) (M.op X0 X2) (M.op X0 X2) X3
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq6390 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op (k X0 X0) (M.op X1 (M.op X2 X3))) X1) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6174 X0 X1 X2 X3 X4
       have i₂ := eq1626 X0
       grind)
    | exact superpose eq1626 eq6174
    | exact resolve eq6174 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6174
  have eq6506 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (k X0 X0) (M.op X1 (M.op X2 X3))) X1) X2) = (M.op (k X4 X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6390 X0 X1 X2 X3 X4
       have i₂ := eq1626 X4
       grind)
    | exact superpose eq1626 eq6390
    | exact resolve eq6390 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6390
  have eq13341 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1622 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq13343 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13341 X0 X1
       have i₂ := eq1626 X0
       grind)
    | exact superpose eq1626 eq13341
    | (have j0 := eq13341 X0 X1
       grind)
    | exact resolve eq13341 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13341
  have eq13562 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13343 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq13343
    | (have j0 := eq13343 X1 (σ X0)
       grind)
    | exact resolve eq13343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13563 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13343 X1 (τ X0)
       have i₂ := eq391 X0 X0
       grind)
    | exact superpose eq391 eq13343
    | (have j0 := eq13343 X1 (τ X0)
       grind)
    | exact resolve eq13343 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq18688 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X2 (σ (k X0 (k X1 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2195 X1 (σ X0) X2
       have i₂ := eq10 X0 (k X1 X1)
       grind)
    | exact superpose eq10 eq2195
    | exact resolve eq2195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq196830 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (k X1 X1) X0)) (M.op X2 (σ X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18688 (M.op (k X1 X1) X0) x X2
       have i₂ := eq1757 x X1 X0
       grind)
    | exact superpose eq1757 eq18688
    | exact resolve eq18688 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757 eq18688
  have eq262609 : ∀ X0 X1 : G, (M.op (σ (M.op (k X0 X0) y)) (M.op X1 (σ y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq196830 y X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq196830
    | (have j0 := eq196830 y X0 X1
       grind)
    | exact resolve eq196830 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196830
  have eq263621 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (σ (M.op (k X1 X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq262609 eq567
    | exact resolve eq567 eq262609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq262609
  have eq263641 : ∀ X0 X1 : G, (M.op (k X0 X0) (σ y)) = (σ (M.op (k X1 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq263621 X0 X1
       have i₂ := eq1626 X0
       grind)
    | exact superpose eq1626 eq263621
    | exact resolve eq263621 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263621
  have eq284758 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (k X1 X1) X0) X2) X0) = (M.op (k X4 X4) (k X2 (k X3 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6506 X1 X2 X0 (k X2 (k X3 X3)) X4
       have i₂ := eq1722 X3 X2 X0
       grind)
    | exact superpose eq1722 eq6506
    | exact resolve eq6506 eq1722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722 eq6506
  have eq285981 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (k X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284758 X0 X1 X2 x x
       have i₂ := eq1764 x X2 x
       grind)
    | exact superpose eq1764 eq284758
    | exact resolve eq284758 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284758
  have eq287075 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X3) (k X0 (k X2 X2))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq285981 (k X0 (k X2 X2)) x X3
       have i₂ := eq1764 x X0 X2
       grind)
    | exact superpose eq1764 eq285981
    | exact resolve eq285981 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764 eq285981
  have eq288096 : ∀ X0 : G, y = (M.op (M.op y x) (k y (k X0 X0))) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq287075 y X0 y
       have i₂ := eq1554
       grind)
    | exact superpose eq1554 eq287075
    | exact resolve eq287075 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq288098 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ x)) (k (σ y) (k X0 X0))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1555 eq287075
    | exact resolve eq287075 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq288498 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq288098 x
       have i₂ := eq287075 sF3 x sF2
       grind)
    | (have i₁ := eq288098 x
       have i₂ := eq287075 x x (M.op (M.op sF3 sF2) (k sF3 (k x x)))
       grind)
    | exact superpose eq287075 eq288098
    | exact resolve eq288098 eq287075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288098
  have eq288499 : x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq288096 x
       have i₂ := eq287075 y x x
       grind)
    | (have i₁ := eq288096 x
       have i₂ := eq287075 x x (M.op (M.op y x) (k y (k x x)))
       grind)
    | exact superpose eq287075 eq288096
    | exact resolve eq288096 eq287075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287075 eq288096
  have eq288671 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq288498
       have i₂ := eq1626 sF2
       grind)
    | exact superpose eq1626 eq288498
    | exact resolve eq288498 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288498
  have eq288672 : (M.op x y) = (k y x) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq288499
       have i₂ := eq1626 x
       grind)
    | exact superpose eq1626 eq288499
    | exact resolve eq288499 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288499
  have eq319009 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq288672
       grind)
    | exact superpose eq288672 eq39
    | exact resolve eq39 eq288672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq288672
  have eq319011 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq319009
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq319009
    | exact resolve eq319009 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319009
  have eq319015 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq319011
    | exact resolve eq319011 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319011
  have eq328492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ x = (k x x) := by
    first
    | exact superpose eq319015 eq288671
    | exact resolve eq288671 eq319015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288671 eq319015
  have eq328505 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    first
    | (have r₁ := eq328492
       have r₂ := eq27
       grind)
    | exact resolve eq328492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328492
  have eq328521 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    first
    | exact superpose eq328505 eq141
    | exact resolve eq141 eq328505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq328851 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq328505 eq13563
    | (have j0 := eq13563 (σ x) X0
       grind)
    | exact resolve eq13563 eq328505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13563 eq328505
  have eq329098 : ∀ X0 : G, (τ (σ x)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq328851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328851
  have eq329230 : ∀ X0 : G, x = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq29 eq329098
    | exact resolve eq329098 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329098
  have eq329492 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq328521
    | exact resolve eq328521 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328521
  have eq329493 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq329492
  have eq329582 : ∀ X0 : G, x = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq329230 X0
       have j1 := eq13343 X0 x
       grind)
    | (have r₁ := eq329230 x
       have r₂ := eq13343 X0 x
       grind)
    | (have r₁ := eq329230 X0
       have r₂ := eq13343 X0 x
       grind)
    | exact resolve eq329230 eq13343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13343 eq329230
  have eq330094 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13562 x X0
       have i₂ := eq329493
       grind)
    | exact superpose eq329493 eq13562
    | (have j0 := eq13562 x X0
       grind)
    | exact resolve eq13562 eq329493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13562 eq329493
  have eq330343 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq330094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330094
  have eq330506 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq330343 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq330343
    | (have j0 := eq330343 X0
       grind)
    | exact resolve eq330343 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330343
  have eq336998 : ∀ X1 : G, (M.op (σ x) (σ y)) = (σ (M.op (k X1 X1) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq263641 x X1
       have i₂ := eq330506 x
       grind)
    | exact superpose eq330506 eq263641
    | exact resolve eq263641 eq330506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263641 eq330506
  have eq337569 : ∀ X1 : G, (M.op (σ x) (σ y)) = (σ (M.op (k X1 X1) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq26 eq336998
    | (have j0 := eq336998 X1
       grind)
    | exact resolve eq336998 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336998
  have eq338481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq329582 eq337569
    | exact resolve eq337569 eq329582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329582 eq337569
  have eq339197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq338481
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq338481
    | exact resolve eq338481 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338481
  have eq339707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq339197
    | exact resolve eq339197 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339197
  have eq339989 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq339707
       have r₂ := eq27
       grind)
    | exact resolve eq339707 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339707
  have eq340096 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq339989 eq31
    | exact resolve eq31 eq339989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq339989
  have eq340244 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq340096
    | exact resolve eq340096 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq340096
  have eq340245 : x = y := by grind
  clear eq340244
  have eq340291 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq340245
       grind)
    | exact superpose eq340245 eq18
    | exact resolve eq18 eq340245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq340292 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq340245
       grind)
    | exact superpose eq340245 eq24
    | exact resolve eq24 eq340245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq340245
  have eq340371 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq340292
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq340292
    | exact resolve eq340292 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq340292
  have eq340372 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq340291
       have i₂ := eq1626 x
       grind)
    | exact superpose eq1626 eq340291
    | exact resolve eq340291 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340291
  have eq340377 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq340371 eq26
    | exact resolve eq26 eq340371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq340371
  have eq340525 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq340377
       have i₂ := eq1626 sF2
       grind)
    | exact superpose eq1626 eq340377
    | exact resolve eq340377 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626 eq340377
  have eq340624 : ∀ X0 : G, (σ (M.op x y)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2443 X0 x
       have i₂ := eq340372
       grind)
    | exact superpose eq340372 eq2443
    | exact resolve eq2443 eq340372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2443
  have eq340649 : ∀ X0 : G, (k X0 X0) = (τ (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2743 x X0
       have i₂ := eq340372
       grind)
    | exact superpose eq340372 eq2743
    | exact resolve eq2743 eq340372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743
  have eq340714 : ∀ X0 : G, (τ (τ (k X0 X0))) = (τ (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq3457 x X0
       have i₂ := eq340372
       grind)
    | exact superpose eq340372 eq3457
    | exact resolve eq3457 eq340372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3457
  have eq340759 : ∀ X0 : G, (τ (k X0 X0)) = (τ (τ (τ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq3998 x X0
       have i₂ := eq340372
       grind)
    | exact superpose eq340372 eq3998
    | exact resolve eq3998 eq340372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3998
  have eq340798 : ∀ X0 : G, (k X0 X0) = (τ (τ (τ (τ (τ (M.op x y)))))) := by
    intro X0
    first
    | (have i₁ := eq5636 x X0
       have i₂ := eq340372
       grind)
    | exact superpose eq340372 eq5636
    | exact resolve eq5636 eq340372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5636 eq340372
  have eq341394 : (τ (τ (M.op x y))) = (τ (τ (τ (τ (M.op x y))))) := by
    first
    | (have i₁ := eq340714 x
       have i₂ := eq340759 x
       grind)
    | exact superpose eq340759 eq340714
    | exact resolve eq340714 eq340759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340714 eq340759
  have eq341469 : (σ (M.op x y)) = (τ (τ (τ (M.op x y)))) := by
    first
    | (have i₁ := eq340624 x
       have i₂ := eq340649 x
       grind)
    | exact superpose eq340649 eq340624
    | exact resolve eq340624 eq340649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340624 eq340649
  have eq341795 : (σ (M.op x y)) = (τ (τ (τ (M.op x y)))) := by
    first
    | exact superpose eq20 eq341469
    | exact resolve eq341469 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq341469
  have eq343690 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq340525 eq1751
    | exact resolve eq1751 eq340525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751 eq340525
  have eq344776 : (M.op (σ x) (σ y)) = (τ (τ (τ (τ (τ (M.op x y)))))) := by
    first
    | (have i₁ := eq343690 x
       have i₂ := eq340798 (M.op sF4 x)
       grind)
    | exact superpose eq340798 eq343690
    | exact resolve eq343690 eq340798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340798 eq343690
  have eq345244 : (M.op (σ x) (σ y)) = (τ (τ (τ (M.op x y)))) := by
    first
    | exact superpose eq341394 eq344776
    | exact resolve eq344776 eq341394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341394 eq344776
  have eq345656 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq341795 eq345244
    | exact resolve eq345244 eq341795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341795 eq345244
  have eq345976 : False := by grind
  exact eq345976

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X2)) = X3 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X2)) = X3 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq36 X0 X1 X2 X3
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq106 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq21 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq367 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq106 X0 X1
       grind)
    | (have i₁ := eq12 X2 X1
       have i₂ := eq106 X1 X0
       grind)
    | exact superpose eq106 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq106 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq106 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 X3 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq45 X1 X3 x X1
       have i₂ := eq106 X0 (M.op X1 x)
       grind)
    | (have i₁ := eq45 X1 X3 x X1
       have i₂ := eq106 (M.op X1 x) X0
       grind)
    | exact superpose eq106 eq45
    | (have j0 := eq45 X1 X3 x X3
       grind)
    | exact resolve eq45 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq106
  have eq389 : ∀ X1 X2 : G, (k X2 X1) = (M.op X1 X2) := by
    intro X1 X2
    first
    | (have j0 := eq367 x X1 X2
       have j1 := eq383 x X1 X2
       grind)
    | (have r₁ := eq367 x X1 X2
       have r₂ := eq383 x X1 x
       grind)
    | (have r₁ := eq367 x (M.op x x) X2
       have r₂ := eq383 x (M.op x x) x
       grind)
    | (have r₁ := eq367 x (k x x) X2
       have r₂ := eq383 x x x
       grind)
    | exact resolve eq367 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq383
  have eq53886 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq389 (σ X0) (σ X1)
       grind)
    | exact superpose eq389 eq15
    | exact resolve eq15 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53901 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53886 X0 X1
       have i₂ := eq389 X0 X1
       grind)
    | exact superpose eq389 eq53886
    | exact resolve eq53886 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq53886
  have eq53916 : False := by grind
  exact eq53916

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pyx_pxx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq47 : ∀ X0 : G, (σ (k X0 (k x x))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq10
    | exact resolve eq10 eq43
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
  have eq52 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq53 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
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
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq85
    | exact resolve eq85 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq108 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq108 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq72
    | exact resolve eq72 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq115 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq49
    | exact resolve eq49 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq116 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq115
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq115
    | exact resolve eq115 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq114
    | exact resolve eq114 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq123 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq99
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq99
    | exact resolve eq99 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq124 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq123
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq123
    | exact resolve eq123 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq433 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
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
  have eq514 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
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
  clear eq51
  have eq532 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X4 x X2
       have i₂ := eq54 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq54 X2 X2 X2 x
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x
       have i₂ := eq54 X1 X0 y x
       grind)
    | (have i₁ := eq52 (M.op y y)
       have i₂ := eq54 y y y x
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq535 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x
       have i₂ := eq54 X0 X1 sF3 x
       grind)
    | (have i₁ := eq53 (M.op sF3 sF3)
       have i₂ := eq54 sF3 sF3 sF3 x
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq585 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq433 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq433 (M.op X0 X0) X1
       grind)
    | exact superpose eq433 eq64
    | (have r₁ := eq64 X1 (M.op X1 X1) X2
       have r₂ := eq433 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq64 X0 (M.op X0 X0) X2
       have r₂ := eq433 X0 (M.op X0 X0)
       grind)
    | exact resolve eq64 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq586 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq585 X0 x X2
       grind)
    | (have r₁ := eq585 X0 x X2
       have r₂ := eq433 X0 x
       grind)
    | (have r₁ := eq585 x X0 X2
       have r₂ := eq433 X0 x
       grind)
    | exact resolve eq585 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq5838 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq435 X1 x X2 x
       have i₂ := eq514 X1 x X2 x X0
       grind)
    | exact superpose eq514 eq435
    | exact resolve eq435 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq6355 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5838 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq435 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq435 eq5838
    | exact resolve eq5838 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq5838
  have eq30045 : ∀ X0 : G, (σ (k X0 (k x x))) = (k (σ X0) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq47
    | exact resolve eq47 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq30046 : ∀ X0 : G, (σ (k X0 (k x x))) = (M.op (M.op (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq30045 X0
       have i₂ := eq586 sF2 (σ X0)
       grind)
    | exact superpose eq586 eq30045
    | exact resolve eq30045 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30045
  have eq30047 : ∀ X0 : G, (σ (k X0 (M.op x x))) = (M.op (M.op (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq30046 X0
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq30046
    | exact resolve eq30046 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq30046
  have eq30048 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ X0)) = (σ (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq30047 X0
       have i₂ := eq586 x X0
       grind)
    | exact superpose eq586 eq30047
    | exact resolve eq30047 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq30047
  have eq35849 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op x x) X0)) (M.op X1 (σ X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq30048 eq14
    | exact resolve eq14 eq30048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30048
  have eq43762 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ (M.op x (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35849 (M.op x (M.op X0 X0)) X1
       have i₂ := eq6355 x X0 x
       grind)
    | exact superpose eq6355 eq35849
    | exact resolve eq35849 eq6355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6355 eq35849
  have eq44021 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ (M.op x (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43762 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43762
    | (have j0 := eq43762 X0 X1
       grind)
    | exact resolve eq43762 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43762
  have eq44106 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X0)) = (σ (M.op x (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq44021 X1 (σ (M.op x (M.op X1 X1)))
       have i₂ := eq433 X0 (σ (M.op x (M.op X1 X1)))
       grind)
    | (have i₁ := eq44021 X1 (σ (M.op x (M.op X1 X1)))
       have i₂ := eq433 (σ (M.op x (M.op X1 X1))) X0
       grind)
    | exact superpose eq433 eq44021
    | exact resolve eq44021 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq44021
  have eq46590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq46591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq46590
    | exact resolve eq46590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46590
  have eq46602 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq46591
       have r₂ := eq27
       grind)
    | exact resolve eq46591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46591
  have eq46606 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq46602
    | exact resolve eq46602 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46602
  have eq46786 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq46606 eq532
    | exact resolve eq532 eq46606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46606
  have eq46800 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq535 eq46786
    | exact resolve eq46786 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq46786
  have eq46827 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq46800 eq124
    | exact resolve eq124 eq46800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq46800
  have eq47044 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq46827
    | exact resolve eq46827 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46827
  have eq47045 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq47044
  have eq47224 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1 y y
       have i₂ := eq47045
       grind)
    | exact superpose eq47045 eq532
    | exact resolve eq532 eq47045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq47045
  have eq47238 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq534 eq47224
    | exact resolve eq47224 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq47224
  have eq47286 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq117
       have i₂ := eq47238
       grind)
    | exact superpose eq47238 eq117
    | exact resolve eq117 eq47238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq47436 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq44106 X0 y
       have i₂ := eq47238
       grind)
    | exact superpose eq47238 eq44106
    | exact resolve eq44106 eq47238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44106 eq47238
  have eq47470 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq47436 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47436
    | (have j0 := eq47436 X0
       grind)
    | exact resolve eq47436 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47436
  have eq47493 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq47286
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47286
    | exact resolve eq47286 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47286
  have eq47496 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq47470
    | (have j0 := eq47470 X0
       grind)
    | exact resolve eq47470 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47470
  have eq100936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq47493 eq47496
    | exact resolve eq47496 eq47493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47493 eq47496
  have eq101025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq100936
  have eq101081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq101025
    | exact resolve eq101025 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101025
  have eq101111 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq101081
       have r₂ := eq27
       grind)
    | exact resolve eq101081 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101081
  have eq101126 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq101111 eq29
    | exact resolve eq29 eq101111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq101111
  have eq101468 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq101126
    | exact resolve eq101126 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq101126
  have eq101469 : x = y := by grind
  clear eq101468
  have eq103760 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq101469
       grind)
    | exact superpose eq101469 eq18
    | exact resolve eq18 eq101469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq103761 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq101469
       grind)
    | exact superpose eq101469 eq24
    | exact resolve eq24 eq101469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq101469
  have eq103911 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq103761
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq103761
    | exact resolve eq103761 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq103761
  have eq103968 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq103911 eq26
    | exact resolve eq26 eq103911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq103911
  have eq104662 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq103968 eq116
    | exact resolve eq116 eq103968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq103968
  have eq104989 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq104662
       have i₂ := eq103760
       grind)
    | exact superpose eq103760 eq104662
    | exact resolve eq104662 eq103760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103760 eq104662
  have eq105024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104989 eq15
    | exact resolve eq15 eq104989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104989
  have eq105110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq105024
    | exact resolve eq105024 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq105024
  have eq105138 : False := by grind
  exact eq105138
