import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_y_pxx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  have eq124 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq229 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq141
    | exact resolve eq141 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq250 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq229
    | exact resolve eq229 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq348 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq398 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq38
    | exact resolve eq38 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq430 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq398 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq398
    | exact resolve eq398 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq450 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq348 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq348
    | exact resolve eq348 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq472 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq450 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq450
    | exact resolve eq450 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq701 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq701 X1 X0
       grind)
    | exact superpose eq701 eq13
    | (have j0 := eq13 X2 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq701 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X0
       have r₂ := eq701 X0 X1
       grind)
    | exact resolve eq13 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq174 X1
       have i₂ := eq701 X1 X0
       grind)
    | exact superpose eq701 eq174
    | exact resolve eq174 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq736 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq701 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq701 X2 X0
       grind)
    | exact superpose eq701 eq16
    | exact resolve eq16 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq472 X1
       have i₂ := eq701 X0 (σ X1)
       grind)
    | (have i₁ := eq472 X1
       have i₂ := eq701 (σ X1) X0
       grind)
    | exact superpose eq701 eq472
    | exact resolve eq472 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq742 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq430 X1
       have i₂ := eq701 X0 (τ X1)
       grind)
    | (have i₁ := eq430 X1
       have i₂ := eq701 (τ X1) X0
       grind)
    | exact superpose eq701 eq430
    | exact resolve eq430 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 : G, x = (k (τ (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq250
       have i₂ := eq701 X0 sF2
       grind)
    | (have i₁ := eq250
       have i₂ := eq701 sF2 x
       grind)
    | exact superpose eq701 eq250
    | exact resolve eq250 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq824 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X1) (k X0 X1)) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op y y) := by
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
  have eq835 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq837 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X0 X0) (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq430 X2
       have i₂ := eq702 (τ X2) X0 X1
       grind)
    | exact superpose eq702 eq430
    | exact resolve eq430 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq702
  have eq1270 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq736 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq736 eq176
    | exact resolve eq176 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1546 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq837 X1
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq837 X0
       have i₂ := eq701 X0 X1
       grind)
    | exact superpose eq701 eq837
    | exact resolve eq837 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1558 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq837 X0
       grind)
    | exact superpose eq837 eq701
    | (have j1 := eq837 X0
       grind)
    | exact resolve eq701 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : ∀ X0 X1 : G, (k (k X0 X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq732 X0 X1
       have i₂ := eq837 X0
       grind)
    | exact superpose eq837 eq732
    | (have j1 := eq837 X0
       grind)
    | exact resolve eq732 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1617 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq837 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq1645 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq834
       grind)
    | exact superpose eq834 eq40
    | exact resolve eq40 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq834
  have eq1646 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1645
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1645
    | exact resolve eq1645 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1648 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1646
    | exact resolve eq1646 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq2230 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq701 X2 X1
       have i₂ := eq1546 X2 X0
       grind)
    | exact superpose eq1546 eq701
    | (have j1 := eq1546 X1 X0
       grind)
    | exact resolve eq701 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2318 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X1 (σ (M.op X1 X1))
       have i₂ := eq1546 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq1546 eq742
    | (have j1 := eq1546 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq742 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2319 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) ∨ (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1172 X1 X2 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       have i₂ := eq1546 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact superpose eq1546 eq1172
    | (have j1 := eq1546 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact resolve eq1172 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq2323 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X1 (τ (M.op X1 X1))
       have i₂ := eq1546 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1546 eq741
    | (have j1 := eq1546 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq741 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2329 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1546 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2333 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2323 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2337 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2319 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2338 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2318 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318
  have eq2391 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (σ (M.op X0 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 x X2
       have i₂ := eq2338 x X0
       grind)
    | exact superpose eq2338 eq176
    | exact resolve eq176 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2498 : ∀ X0 X1 : G, (k x (M.op X1 X1)) = (τ (k (σ x) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (M.op X1 X1)
       have i₂ := eq2338 X0 X1
       grind)
    | exact superpose eq2338 eq44
    | exact resolve eq44 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq2500 : ∀ X0 X1 : G, (k (M.op x y) (M.op X1 X1)) = (τ (k (σ (M.op x y)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X1)
       have i₂ := eq2338 X0 X1
       grind)
    | exact superpose eq2338 eq50
    | exact resolve eq50 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq2511 : ∀ X0 X1 : G, (k (M.op x y) (M.op X1 X1)) = (k (M.op x y) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq124 eq2500
    | exact resolve eq2500 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq2500
  have eq2513 : ∀ X0 X1 : G, (k x (M.op X1 X1)) = (k x (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq90 eq2498
    | exact resolve eq2498 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq2498
  have eq2567 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2333 X2 (M.op X1 X1)
       have i₂ := eq1270 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq2333 X2 (M.op X1 X1)
       have i₂ := eq1270 (M.op X1 X1) X0 X1
       grind)
    | exact superpose eq1270 eq2333
    | exact resolve eq2333 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333
  have eq7594 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1617 X1
       have i₂ := eq1558 X1 X0
       grind)
    | exact superpose eq1558 eq1617
    | (have j0 := eq1617 X1
       have j1 := eq1558 X1 X1
       grind)
    | (have r₁ := eq1617 (M.op X1 X1)
       have r₂ := eq1558 (M.op X1 X1) X1
       grind)
    | exact resolve eq1617 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558 eq1617
  have eq7613 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7594 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7594
  have eq16479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1648 eq835
    | exact resolve eq835 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq16488 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16479
       have r₂ := eq27
       grind)
    | exact resolve eq16479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16479
  have eq16523 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16488 eq741
    | exact resolve eq741 eq16488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq16529 : x = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq16488 eq747
    | exact resolve eq747 eq16488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq16488
  have eq16759 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq16529
    | exact resolve eq16529 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16529
  have eq16761 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq16523
    | exact resolve eq16523 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16523
  have eq16832 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq730 x x x
       grind)
    | (have r₁ := eq16759
       have r₂ := eq730 y x x
       grind)
    | exact resolve eq16759 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16759
  have eq16834 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16761 X0
       have j1 := eq730 X0 X0 x
       grind)
    | (have r₁ := eq16761 (M.op X0 X0)
       have r₂ := eq730 X0 x (k x (M.op X0 X0))
       grind)
    | (have r₁ := eq16761 X0
       have r₂ := eq730 y x x
       grind)
    | exact resolve eq16761 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16761
  have eq16978 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k x (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2513 X0 X1
       have i₂ := eq16834 (τ (M.op X0 X0))
       grind)
    | exact superpose eq16834 eq2513
    | exact resolve eq2513 eq16834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513
  have eq16984 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2329 X0 x
       have i₂ := eq16834 x
       grind)
    | exact superpose eq16834 eq2329
    | (have j0 := eq2329 X0 x
       grind)
    | (have r₁ := eq2329 X0 x
       have r₂ := eq16834 x
       grind)
    | exact resolve eq2329 eq16834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16834
  have eq16994 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16984 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16984
  have eq17008 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16994 eq16978
    | exact resolve eq16978 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16978
  have eq17019 : ∀ X0 : G, x = (τ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16832 eq17008
    | exact resolve eq17008 eq16832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16832 eq17008
  have eq17027 : x = (τ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16994 eq17019
    | exact resolve eq17019 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17019
  have eq17037 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 x
       have i₂ := eq17027
       grind)
    | exact superpose eq17027 eq14
    | exact resolve eq14 eq17027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17027
  have eq17038 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq17037
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17037
    | exact resolve eq17037 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17037
  have eq17044 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq17038 eq31
    | exact resolve eq31 eq17038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17081 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq17044
    | exact resolve eq17044 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17044
  have eq17082 : x = (σ x) ∨ x = y := by grind
  clear eq17081
  have eq17083 : (M.op x y) = (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq17082
       grind)
    | exact superpose eq17082 eq18
    | exact resolve eq18 eq17082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17084 : (σ x) = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq17082
       grind)
    | exact superpose eq17082 eq22
    | exact resolve eq22 eq17082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17085 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (σ x) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq17082
       grind)
    | exact superpose eq17082 eq35
    | exact resolve eq35 eq17082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq17086 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq17082
       grind)
    | exact superpose eq17082 eq39
    | exact resolve eq39 eq17082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq17301 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (σ x)))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2391 x X0 X1
       have i₂ := eq16994 x
       grind)
    | exact superpose eq16994 eq2391
    | exact resolve eq2391 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq17397 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) x) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X1
       have i₂ := eq16994 X1
       grind)
    | exact superpose eq16994 eq16
    | exact resolve eq16 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17415 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2337 X0 x x
       have i₂ := eq16994 (M.op x x)
       grind)
    | exact superpose eq16994 eq2337
    | exact resolve eq2337 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337
  have eq17493 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17415 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17415
    | (have j0 := eq17415 X0
       grind)
    | exact resolve eq17415 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17415
  have eq17507 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq16994 eq17397
    | exact resolve eq17397 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17397
  have eq17596 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (σ x)))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq17301 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17301
    | (have j0 := eq17301 X0 X1
       grind)
    | exact resolve eq17301 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17301
  have eq17742 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq17038 eq17507
    | exact resolve eq17507 eq17038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17038 eq17507
  have eq19685 : (σ (σ (M.op x y))) = (k (σ x) (σ (σ y))) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1648 eq17085
    | exact resolve eq17085 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648 eq17085
  have eq19707 : (σ (σ (M.op x y))) = (k (σ x) (σ (σ y))) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq19685
  have eq19731 : (σ (σ (M.op x y))) = (k (σ x) (σ (σ y))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq17082 eq19707
    | exact resolve eq19707 eq17082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19707
  have eq19734 : (σ (σ (M.op x y))) = (k (σ x) (σ (σ x))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq17493 eq19731
    | (have j1 := eq17493 y
       grind)
    | exact resolve eq19731 eq17493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17493 eq19731
  have eq19735 : (k (σ x) (σ x)) = (σ (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq17084 eq19734
    | exact resolve eq19734 eq17084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17084 eq19734
  have eq20020 : y = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq17083 eq17742
    | exact resolve eq17742 eq17083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17742
  have eq20057 : y = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20020
  have eq21447 : (k x x) = (τ (σ (σ (M.op x y)))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq19735 eq97
    | exact resolve eq97 eq19735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19735
  have eq21470 : (σ (M.op x y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq21447
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq21447
    | exact resolve eq21447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21447
  have eq21477 : (σ x) = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq17082 eq21470
    | exact resolve eq21470 eq17082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21470
  have eq21503 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq701 y X0
       have i₂ := eq21477
       grind)
    | exact superpose eq21477 eq701
    | exact resolve eq701 eq21477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21507 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq732 y X0
       have i₂ := eq21477
       grind)
    | exact superpose eq21477 eq732
    | exact resolve eq732 eq21477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq21477
  have eq21992 : ∀ X0 : G, (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq21503 eq97
    | (have j1 := eq21503 X0
       grind)
    | exact resolve eq97 eq21503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq21998 : ∀ X0 X1 : G, (k (σ (M.op x y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq21503 eq1563
    | (have j0 := eq1563 (σ x) X1
       have j1 := eq21503 (σ x)
       grind)
    | exact resolve eq1563 eq21503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21503
  have eq22011 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ (M.op x y)) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21998 X0 (σ x)
       have j1 := eq7613 X0 (σ x)
       grind)
    | (have r₁ := eq21998 (M.op X0 X0) x
       have r₂ := eq7613 X0 (k (σ (M.op x y)) (M.op X0 X0))
       grind)
    | (have r₁ := eq21998 X0 x
       have r₂ := eq7613 (σ x) (σ x)
       grind)
    | (have r₁ := eq21998 X0 X0
       have r₂ := eq7613 X0 (σ x)
       grind)
    | exact resolve eq21998 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21998
  have eq22016 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq28 eq21992
    | (have j0 := eq21992 X0
       grind)
    | exact resolve eq21992 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21992
  have eq22022 : ∀ X0 : G, (M.op x y) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq17082 eq22016
    | (have j0 := eq22016 X0
       grind)
    | exact resolve eq22016 eq17082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22016
  have eq23201 : ∀ X0 X1 : G, (k (σ (M.op x y)) X1) = X1 ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq22011 (M.op X0 X0)
       grind)
    | exact superpose eq22011 eq701
    | (have j1 := eq22011 X1
       grind)
    | exact resolve eq701 eq22011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23207 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ (k (σ (M.op x y)) X2) = X2 ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq736 X0 X1 X2
       have i₂ := eq22011 (M.op X0 X0)
       grind)
    | exact superpose eq22011 eq736
    | (have j1 := eq22011 X2
       grind)
    | exact resolve eq736 eq22011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq23252 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ (k (σ (M.op x y)) X2) = X2 ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1270 X0 X1 X2
       have i₂ := eq22011 (M.op X2 X2)
       grind)
    | exact superpose eq22011 eq1270
    | (have j1 := eq22011 X2
       grind)
    | exact resolve eq1270 eq22011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270 eq22011
  have eq23463 : ∀ X1 X2 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ (k (σ (M.op x y)) X2) = X2 ∨ x = y := by
    intro X1 X2
    first
    | exact superpose eq23252 eq23207
    | (have j0 := eq23207 x X1 X2
       have j1 := eq23252 x X1 X2
       grind)
    | exact resolve eq23207 eq23252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23207 eq23252
  have eq23687 : ∀ X0 X1 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (k (σ x) X0) = X0 ∨ x = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq22022 eq21507
    | (have j0 := eq21507 X0
       have j1 := eq22022 X1
       grind)
    | exact resolve eq21507 eq22022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21507
  have eq23694 : ∀ X0 X1 : G, (k (M.op x y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq22022 eq1563
    | (have j0 := eq1563 (σ x) X1
       have j1 := eq22022 (σ x)
       grind)
    | exact resolve eq1563 eq22022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq22022
  have eq23702 : ∀ X0 X1 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (k (σ x) X0) = X0 ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq23687 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23687
  have eq23713 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k (M.op x y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq23694 X0 (σ x)
       have j1 := eq7613 X0 (σ x)
       grind)
    | (have r₁ := eq23694 (M.op X0 X0) x
       have r₂ := eq7613 X0 (k (M.op x y) (M.op X0 X0))
       grind)
    | (have r₁ := eq23694 X0 x
       have r₂ := eq7613 (σ x) (σ x)
       grind)
    | (have r₁ := eq23694 X0 X0
       have r₂ := eq7613 X0 (σ x)
       grind)
    | exact resolve eq23694 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7613 eq23694
  have eq23718 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq23702 X0 x
       have j1 := eq730 X0 X0 (σ x)
       grind)
    | (have r₁ := eq23702 (M.op X0 X0) x
       have r₂ := eq730 X0 x (k (σ x) (M.op X0 X0))
       grind)
    | (have r₁ := eq23702 X0 X0
       have r₂ := eq730 X0 x (σ x)
       grind)
    | exact resolve eq23702 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23702
  have eq23760 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq23718 eq2329
    | (have j0 := eq2329 X0 (σ x)
       grind)
    | (have r₁ := eq2329 X0 (σ x)
       have r₂ := eq23718 (σ x)
       grind)
    | exact resolve eq2329 eq23718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23718
  have eq23774 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq23760 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23760
  have eq24076 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X1
       have i₂ := eq23774 X1
       grind)
    | exact superpose eq23774 eq16
    | exact resolve eq16 eq23774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24211 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X1
    first
    | exact superpose eq23774 eq24076
    | exact resolve eq24076 eq23774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24076
  have eq27291 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq23201 eq2329
    | (have j0 := eq2329 X0 (σ (M.op x y))
       have j1 := eq23201 X1 X1
       grind)
    | (have r₁ := eq2329 X0 (σ (M.op x y))
       have r₂ := eq23201 X0 (σ (M.op x y))
       grind)
    | exact resolve eq2329 eq23201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23201
  have eq27307 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq27291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27291
  have eq27325 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq23774 eq27307
    | (have j0 := eq27307 X0 X1
       have j1 := eq23774 X1
       grind)
    | exact resolve eq27307 eq23774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23774 eq27307
  have eq27417 : ∀ X0 X1 : G, (σ x) = (k X0 X0) ∨ (σ x) = X0 ∨ (k (M.op x y) X1) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1546 X0 X1
       have i₂ := eq23713 (M.op X0 X0)
       grind)
    | exact superpose eq23713 eq1546
    | (have j1 := eq23713 X1
       grind)
    | exact resolve eq1546 eq23713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq28311 : ∀ X0 : G, (M.op x y) ≠ (σ x) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq27325 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27325
  have eq29474 : y = (M.op (M.op x y) (σ x)) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq17083 eq24211
    | exact resolve eq24211 eq17083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24211
  have eq29525 : y = (M.op (M.op x y) (σ x)) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq29474
  have eq34402 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20057 eq17596
    | exact resolve eq17596 eq20057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17596 eq20057
  have eq34537 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq34402 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34402
  have eq40669 : ∀ X0 : G, y = (M.op (M.op x y) (σ x)) ∨ (k (σ (M.op x y)) X0) = X0 ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq17083 eq23463
    | (have j0 := eq23463 x X0
       grind)
    | exact resolve eq23463 eq17083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17083 eq23463
  have eq40744 : ∀ X0 : G, y = (M.op (M.op x y) (σ x)) ∨ (k (σ (M.op x y)) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq40669 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40669
  have eq40776 : ∀ X0 : G, y = (M.op (M.op x y) (σ x)) ∨ (k (M.op x y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq29525 eq40744
    | exact resolve eq40744 eq29525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29525 eq40744
  have eq40841 : ∀ X0 : G, y = (k (M.op x y) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ (k (M.op x y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq40776 (M.op X0 x)
       grind)
    | exact superpose eq40776 eq11
    | (have j0 := eq11 (M.op x y) (σ x)
       have j1 := eq40776 X0
       grind)
    | exact resolve eq11 eq40776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40776
  have eq40861 : ∀ X0 : G, y = (k (M.op x y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ (k (M.op x y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq40841 X0
       have j1 := eq28311 (σ x)
       grind)
    | (have r₁ := eq40841 X0
       have r₂ := eq28311 X0
       grind)
    | exact resolve eq40841 eq28311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40841
  have eq40867 : ∀ X0 : G, y = (k (M.op x y) (σ x)) ∨ (k (M.op x y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq40861 X0
       have j1 := eq730 X0 X0 (M.op x y)
       grind)
    | (have r₁ := eq40861 X0
       have r₂ := eq730 (σ x) x (M.op x y)
       grind)
    | (have r₁ := eq40861 (M.op X0 X0)
       have r₂ := eq730 X0 x (k (M.op x y) (M.op X0 X0))
       grind)
    | exact resolve eq40861 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq40861
  have eq40876 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (k (M.op x y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17086 X0
       have i₂ := eq40867 (k X0 sF2)
       grind)
    | exact superpose eq40867 eq17086
    | (have j1 := eq40867 X0
       grind)
    | exact resolve eq17086 eq40867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17086 eq40867
  have eq40880 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (k (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq40876 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40876
  have eq40885 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (k (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq40880
    | (have j0 := eq40880 X0
       grind)
    | exact resolve eq40880 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40880
  have eq40888 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (k (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40885 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40885
    | (have j0 := eq40885 X0
       grind)
    | exact resolve eq40885 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40885
  have eq40898 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (k (M.op x y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1 x
       have i₂ := eq40888 (k X0 X1)
       grind)
    | exact superpose eq40888 eq824
    | (have j0 := eq824 (σ (M.op x y)) (σ x) x
       have j1 := eq40888 X1
       grind)
    | exact resolve eq824 eq40888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq40888
  have eq40902 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (k (M.op x y) X1) = X1 := by
    intro X1
    first
    | exact superpose eq2230 eq40898
    | (have j0 := eq40898 x X1
       have j1 := eq2230 (σ (M.op x y)) X1 (σ x)
       grind)
    | exact resolve eq40898 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230 eq40898
  have eq40906 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (k (M.op x y) X1) = X1 := by
    intro X1
    first
    | exact superpose eq23713 eq40902
    | (have j0 := eq40902 X1
       have j1 := eq23713 X1
       grind)
    | exact resolve eq40902 eq23713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40902
  have eq40907 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (k (M.op x y) X1) = X1 := by
    intro X1
    first
    | (have j0 := eq40906 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40906
  have eq40911 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (k (M.op x y) X1) = X1 := by
    intro X1
    first
    | exact superpose eq27417 eq40907
    | (have j0 := eq40907 X1
       have j1 := eq27417 (σ (M.op x y)) X1
       grind)
    | exact resolve eq40907 eq27417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27417 eq40907
  have eq40914 : ∀ X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (k (M.op x y) X1) = X1 := by
    intro X1
    first
    | exact superpose eq23713 eq40911
    | (have j0 := eq40911 X1
       have j1 := eq23713 X1
       grind)
    | exact resolve eq40911 eq23713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23713 eq40911
  have eq40915 : ∀ X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (k (M.op x y) X1) = X1 := by
    intro X1
    first
    | exact superpose eq26 eq40914
    | (have j0 := eq40914 X1
       grind)
    | exact resolve eq40914 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40914
  have eq40916 : ∀ X1 : G, (k (M.op x y) X1) = X1 ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X1
    first
    | (have j0 := eq40915 X1
       grind)
    | (have r₁ := eq40915 X1
       have r₂ := eq27
       grind)
    | exact resolve eq40915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40915
  have eq40934 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op x y) (τ (M.op X1 X1))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq40916 eq2511
    | exact resolve eq2511 eq40916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq40955 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq40916 eq2329
    | (have j0 := eq2329 X0 (M.op x y)
       grind)
    | (have r₁ := eq2329 X0 (M.op x y)
       have r₂ := eq40916 (M.op x y)
       grind)
    | exact resolve eq2329 eq40916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329
  have eq40981 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq40955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40955
  have eq41031 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x y) (τ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq40981 eq40934
    | exact resolve eq40934 eq40981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40934
  have eq41048 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq40916 eq41031
    | exact resolve eq41031 eq40916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40916 eq41031
  have eq41057 : (M.op x y) = (τ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq40981 eq41048
    | exact resolve eq41048 eq40981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41048
  have eq41067 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq41057 eq14
    | exact resolve eq14 eq41057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41057
  have eq41080 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq41067
    | exact resolve eq41067 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41067
  have eq41082 : (M.op x y) = (τ (σ x)) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41080 eq28
    | exact resolve eq28 eq41080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41121 : (M.op x y) ≠ (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq41080
  have eq41159 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29 eq41082
    | exact resolve eq41082 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41082
  have eq41172 : (M.op x y) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17082 eq41159
    | exact resolve eq41159 eq17082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17082 eq41159
  have eq41181 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq41172
       have r₂ := eq41121
       grind)
    | exact resolve eq41172 eq41121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41121 eq41172
  have eq41183 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq41181 eq28
    | exact resolve eq28 eq41181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq41563 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq2567 x x X0
       have i₂ := eq40981 (M.op x x)
       grind)
    | exact superpose eq40981 eq2567
    | exact resolve eq2567 eq40981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567 eq40981
  have eq41720 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ x) := by
    intro X0
    first
    | exact superpose eq41181 eq41563
    | (have j0 := eq41563 X0
       grind)
    | exact resolve eq41563 eq41181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41181 eq41563
  have eq42019 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ x = y ∨ (M.op x y) = (σ x) := by
    intro X0
    first
    | exact superpose eq41183 eq41720
    | exact resolve eq41720 eq41183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41183 eq41720
  have eq42272 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq42019 X0
       have j1 := eq28311 X0
       grind)
    | (have r₁ := eq42019 X0
       have r₂ := eq28311 X0
       grind)
    | exact resolve eq42019 eq28311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28311 eq42019
  have eq43130 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq34537 y
       have i₂ := eq42272 y
       grind)
    | exact superpose eq42272 eq34537
    | exact resolve eq34537 eq42272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34537 eq42272
  have eq43227 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq43130
  have eq43321 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16994 eq43227
    | exact resolve eq43227 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16994 eq43227
  have eq43322 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq43321
  have eq44501 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq43322 eq31
    | exact resolve eq31 eq43322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq43322
  have eq44557 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq44501
    | exact resolve eq44501 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44501
  have eq44558 : x = y := by grind
  clear eq44557
  have eq44579 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq44558
       grind)
    | exact superpose eq44558 eq18
    | exact resolve eq18 eq44558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq44580 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq44558
       grind)
    | exact superpose eq44558 eq24
    | exact resolve eq24 eq44558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq44558
  have eq44603 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq44580
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44580
    | exact resolve eq44580 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq44580
  have eq44604 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq44603 eq26
    | exact resolve eq26 eq44603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq44603
  have eq44679 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq701 x X0
       have i₂ := eq44579
       grind)
    | exact superpose eq44579 eq701
    | exact resolve eq701 eq44579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44744 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2338 X0 x
       have i₂ := eq44579
       grind)
    | exact superpose eq44579 eq2338
    | exact resolve eq2338 eq44579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq44579
  have eq44901 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq44744
    | (have j0 := eq44744 X0
       grind)
    | exact resolve eq44744 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq44744
  have eq44987 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq44901 x
       have i₂ := eq44679 x
       grind)
    | exact superpose eq44679 eq44901
    | exact resolve eq44901 eq44679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44901
  have eq45283 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq44604 eq701
    | exact resolve eq701 eq44604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq44604
  have eq45554 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45283 x
       have i₂ := eq44679 x
       grind)
    | exact superpose eq44679 eq45283
    | exact resolve eq45283 eq44679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44679 eq45283
  have eq45836 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq45554 eq27
    | exact resolve eq27 eq45554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq45554
  have eq45867 : False := by grind
  exact eq45867

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_y_pxx_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq177 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq178 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
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
  have eq257 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) y) := by
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
  have eq278 : y = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq31 eq257
    | exact resolve eq257 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq348 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq398 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq38
    | exact resolve eq38 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq430 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq398 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq398
    | exact resolve eq398 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq450 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq348 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq348
    | exact resolve eq348 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq348
  have eq472 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq450 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq450
    | exact resolve eq450 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq701 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq701 X1 X0
       grind)
    | exact superpose eq701 eq13
    | (have j0 := eq13 X2 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq701 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X0
       have r₂ := eq701 X0 X1
       grind)
    | exact resolve eq13 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq701 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq701 X2 X0
       grind)
    | exact superpose eq701 eq16
    | exact resolve eq16 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq472 X1
       have i₂ := eq701 X0 (σ X1)
       grind)
    | (have i₁ := eq472 X1
       have i₂ := eq701 (σ X1) X0
       grind)
    | exact superpose eq701 eq472
    | exact resolve eq472 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq742 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq430 X1
       have i₂ := eq701 X0 (τ X1)
       grind)
    | (have i₁ := eq430 X1
       have i₂ := eq701 (τ X1) X0
       grind)
    | exact superpose eq701 eq430
    | exact resolve eq430 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 : G, y = (k (τ (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq278
       have i₂ := eq701 X0 sF3
       grind)
    | (have i₁ := eq278
       have i₂ := eq701 sF3 x
       grind)
    | exact superpose eq701 eq278
    | exact resolve eq278 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq828 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 X1)) (M.op X2 X0)) = X2 ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq11 X0 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (k X0 (M.op X1 X1)) (M.op X2 X0)) X2
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) := by
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
  have eq835 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq843 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X0 X0) (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq430 X2
       have i₂ := eq702 (τ X2) X0 X1
       grind)
    | exact superpose eq702 eq430
    | exact resolve eq430 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq702
  have eq1552 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq843 X1
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq843 X0
       have i₂ := eq701 X0 X1
       grind)
    | exact superpose eq701 eq843
    | exact resolve eq843 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq843 X0
       grind)
    | exact superpose eq843 eq701
    | (have j1 := eq843 X0
       grind)
    | exact resolve eq701 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1623 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1651 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq834
       grind)
    | exact superpose eq834 eq39
    | exact resolve eq39 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq834
  have eq1652 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1651
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1651
    | exact resolve eq1651 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq1654 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1652
    | exact resolve eq1652 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq2236 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq701 X2 X1
       have i₂ := eq1552 X2 X0
       grind)
    | exact superpose eq1552 eq701
    | (have j1 := eq1552 X1 X0
       grind)
    | exact resolve eq701 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2324 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X1 (σ (M.op X1 X1))
       have i₂ := eq1552 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq1552 eq742
    | (have j1 := eq1552 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq742 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2325 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) ∨ (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1178 X1 X2 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       have i₂ := eq1552 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact superpose eq1552 eq1178
    | (have j1 := eq1552 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact resolve eq1178 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq2329 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X1 (τ (M.op X1 X1))
       have i₂ := eq1552 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1552 eq741
    | (have j1 := eq1552 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq741 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2335 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1552 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq2339 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329
  have eq2343 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2325 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325
  have eq2344 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2324 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2324
  have eq2395 : ∀ X0 X2 X3 : G, (M.op (M.op (σ (M.op X0 X0)) X2) (M.op X3 X2)) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X3 x X2
       have i₂ := eq2344 x X0
       grind)
    | exact superpose eq2344 eq16
    | exact resolve eq16 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2397 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (σ (M.op X0 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 x X2
       have i₂ := eq2344 x X0
       grind)
    | exact superpose eq2344 eq176
    | exact resolve eq176 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2399 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op X0 X0)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 x
       have i₂ := eq2344 x X0
       grind)
    | exact superpose eq2344 eq178
    | exact resolve eq178 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2505 : ∀ X0 X1 : G, (k y (M.op X1 X1)) = (τ (k (σ y) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X1 X1)
       have i₂ := eq2344 X0 X1
       grind)
    | exact superpose eq2344 eq47
    | exact resolve eq47 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq2518 : ∀ X0 X1 : G, (k y (M.op X1 X1)) = (k y (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq107 eq2505
    | exact resolve eq2505 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq2505
  have eq2650 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (τ (M.op X0 X0)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq736 X2 X1 (M.op X1 X1)
       have i₂ := eq2339 (M.op X1 X1) X0
       grind)
    | exact superpose eq2339 eq736
    | exact resolve eq736 eq2339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq2339
  have eq4003 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 x
       have i₂ := eq179 X1 X0 y x
       grind)
    | (have i₁ := eq177 (M.op y y)
       have i₂ := eq179 y y y x
       grind)
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq179
  have eq7693 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1623 X1
       have i₂ := eq1564 X1 X0
       grind)
    | exact superpose eq1564 eq1623
    | (have j0 := eq1623 X1
       have j1 := eq1564 X1 X1
       grind)
    | (have r₁ := eq1623 (M.op X1 X1)
       have r₂ := eq1564 (M.op X1 X1) X1
       grind)
    | exact resolve eq1623 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564 eq1623
  have eq7712 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7693 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7693
  have eq21379 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq1654 eq835
    | exact resolve eq835 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq1654
  have eq21388 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq21379
       have r₂ := eq27
       grind)
    | exact resolve eq21379 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21379
  have eq21572 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21388 eq741
    | exact resolve eq741 eq21388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq21579 : y = (k (τ (σ y)) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq21388 eq748
    | exact resolve eq748 eq21388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq21685 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (τ (σ y)) (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq21388 eq2650
    | exact resolve eq2650 eq21388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650 eq21388
  have eq21782 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq31 eq21685
    | exact resolve eq21685 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21685
  have eq21864 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq21579
    | exact resolve eq21579 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21579
  have eq21867 : ∀ X0 : G, (k y X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq31 eq21572
    | exact resolve eq21572 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21572
  have eq21903 : ∀ X0 : G, (M.op X0 X0) = (M.op y (k y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2236 eq21782
    | (have j1 := eq2236 (M.op y (k y y)) x X0
       grind)
    | exact resolve eq21782 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21782
  have eq21955 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq730 x y y
       grind)
    | (have r₁ := eq21864
       have r₂ := eq730 x x y
       grind)
    | exact resolve eq21864 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21864
  have eq21958 : ∀ X0 : G, (k y X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21867 X0
       have j1 := eq730 X0 X0 y
       grind)
    | (have r₁ := eq21867 (M.op X0 X0)
       have r₂ := eq730 X0 x (k y (M.op X0 X0))
       grind)
    | (have r₁ := eq21867 X0
       have r₂ := eq730 x x y
       grind)
    | exact resolve eq21867 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq21867
  have eq21976 : (k y y) = (M.op y (k y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq2236 eq21903
    | (have j1 := eq2236 y x x
       grind)
    | exact resolve eq21903 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236 eq21903
  have eq22027 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq21958 eq21976
    | exact resolve eq21976 eq21958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21976
  have eq22069 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq7712 x y
       grind)
    | (have r₁ := eq22027
       have r₂ := eq7712 y y
       grind)
    | (have r₁ := eq22027
       have r₂ := eq7712 x y
       grind)
    | exact resolve eq22027 eq7712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7712 eq22027
  have eq22131 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k y (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2518 X0 X1
       have i₂ := eq21958 (τ (M.op X0 X0))
       grind)
    | exact superpose eq21958 eq2518
    | exact resolve eq2518 eq21958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518
  have eq22137 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2335 X0 y
       have i₂ := eq21958 y
       grind)
    | exact superpose eq21958 eq2335
    | (have j0 := eq2335 X0 y
       grind)
    | (have r₁ := eq2335 X0 y
       have r₂ := eq21958 y
       grind)
    | exact resolve eq2335 eq21958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335 eq21958
  have eq22148 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq22137 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22137
  have eq22163 : ∀ X0 : G, (k y y) = (τ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22148 eq22131
    | exact resolve eq22131 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22131
  have eq22174 : ∀ X0 : G, y = (τ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq21955 eq22163
    | exact resolve eq22163 eq21955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21955 eq22163
  have eq22182 : y = (τ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22148 eq22174
    | exact resolve eq22174 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22174
  have eq22192 : y = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq22182
       grind)
    | exact superpose eq22182 eq14
    | exact resolve eq14 eq22182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22182
  have eq22193 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22192
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22192
    | exact resolve eq22192 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22192
  have eq22199 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq22193 eq31
    | exact resolve eq31 eq22193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22240 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq22199
    | exact resolve eq22199 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22199
  have eq22241 : y = (σ y) ∨ x = y := by grind
  clear eq22240
  have eq22242 : (M.op x y) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq22241
       grind)
    | exact superpose eq22241 eq18
    | exact resolve eq18 eq22241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22245 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq22241
       grind)
    | exact superpose eq22241 eq40
    | exact resolve eq40 eq22241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq22268 : x ≠ (σ y) ∨ x = y := by grind
  have eq22485 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (σ y)))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2397 x X0 X1
       have i₂ := eq22148 x
       grind)
    | exact superpose eq22148 eq2397
    | exact resolve eq2397 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq22487 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2399 x
       have i₂ := eq22148 x
       grind)
    | exact superpose eq22148 eq2399
    | exact resolve eq2399 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq22616 : ∀ X0 X1 : G, (M.op (k X0 (M.op X1 X1)) y) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1 X0
       have i₂ := eq22148 X0
       grind)
    | exact superpose eq22148 eq828
    | (have j0 := eq828 X0 X1 x
       grind)
    | exact resolve eq828 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq22642 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2343 X0 x x
       have i₂ := eq22148 (M.op x x)
       grind)
    | exact superpose eq22148 eq2343
    | exact resolve eq2343 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq22656 : x = (M.op (M.op y y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4003 y y
       have i₂ := eq22148 (M.op y y)
       grind)
    | exact superpose eq22148 eq4003
    | exact resolve eq4003 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4003
  have eq22657 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op X0 X0))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op X0 X0)
       have i₂ := eq22148 (M.op X0 X0)
       grind)
    | exact superpose eq22148 eq16
    | exact resolve eq16 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22716 : ∀ X1 : G, (M.op y (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq22148 eq22657
    | exact resolve eq22657 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22657
  have eq22717 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22069 eq22656
    | exact resolve eq22656 eq22069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22656
  have eq22727 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22642 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22642
    | (have j0 := eq22642 X0
       grind)
    | exact resolve eq22642 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22642
  have eq22748 : ∀ X0 X1 : G, (M.op (k X0 y) y) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq22148 eq22616
    | (have j0 := eq22616 X0 X1
       grind)
    | exact resolve eq22616 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22616
  have eq22863 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22487
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22487
    | exact resolve eq22487 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22487
  have eq22865 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (σ y)))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq22485 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22485
    | (have j0 := eq22485 X0 X1
       grind)
    | exact resolve eq22485 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22485
  have eq23004 : ∀ X1 : G, (M.op (σ y) (M.op X1 (σ y))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq22193 eq22716
    | exact resolve eq22716 eq22193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22716
  have eq23005 : x = (M.op (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22193 eq22717
    | exact resolve eq22717 eq22193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22717
  have eq23026 : ∀ X0 X1 : G, (M.op (k X0 y) y) = X0 ∨ y = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq22148 eq22748
    | (have j0 := eq22748 X0 (M.op X1 X1)
       grind)
    | exact resolve eq22748 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22748
  have eq23120 : (σ x) = (M.op y (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22148 eq22863
    | exact resolve eq22863 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22863
  have eq23227 : ∀ X0 : G, (M.op (k X0 y) y) = X0 ∨ y = X0 ∨ (M.op y y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22148 eq23026
    | (have j0 := eq23026 X0 x
       grind)
    | exact resolve eq23026 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23026
  have eq23295 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22193 eq23120
    | exact resolve eq23120 eq22193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23120
  have eq23353 : ∀ X0 : G, (M.op (k X0 y) y) = X0 ∨ y = X0 ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22069 eq23227
    | (have j0 := eq23227 X0
       grind)
    | exact resolve eq23227 eq22069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22069 eq23227
  have eq23354 : ∀ X0 : G, (M.op (k X0 y) y) = X0 ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq23353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23353
  have eq23411 : ∀ X0 : G, (M.op (k X0 (σ y)) (σ y)) = X0 ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22193 eq23354
    | (have j0 := eq23354 X0
       grind)
    | exact resolve eq23354 eq22193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23354
  have eq23429 : ∀ X0 : G, (M.op (k X0 (σ y)) (σ y)) = X0 ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22193 eq23411
    | (have j0 := eq23411 X0
       grind)
    | exact resolve eq23411 eq22193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23411
  have eq30408 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq22242 eq22865
    | exact resolve eq22865 eq22242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22242 eq22865
  have eq30529 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30408 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30408
  have eq31135 : ∀ X0 X1 : G, x = (M.op (M.op (σ (M.op X1 X1)) (M.op X0 (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq30529 eq2395
    | exact resolve eq2395 eq30529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395 eq30529
  have eq31148 : ∀ X0 : G, x = (M.op (M.op (σ y) (M.op X0 (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22148 eq31135
    | exact resolve eq31135 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22148 eq31135
  have eq31194 : ∀ X0 : G, x = (M.op (M.op (σ y) (M.op X0 (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq31148 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31148
    | (have j0 := eq31148 X0
       grind)
    | exact resolve eq31148 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31148
  have eq41181 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23429 eq23004
    | (have j1 := eq23429 (σ x)
       grind)
    | exact resolve eq23004 eq23429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23004
  have eq41192 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = X0 := by
    intro X0
    first
    | (have j0 := eq41181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41181
  have eq43397 : x = (k (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq41192 eq23005
    | (have j1 := eq41192 (σ x)
       grind)
    | exact resolve eq23005 eq41192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23005 eq41192
  have eq43455 : x = (k (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq43397
  have eq43615 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq43455 eq22245
    | exact resolve eq22245 eq43455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22245 eq43455
  have eq43619 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by grind
  clear eq43615
  have eq43623 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq43619
    | exact resolve eq43619 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43619
  have eq43626 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq43623
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43623
    | exact resolve eq43623 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43623
  have eq43632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq43626 eq23429
    | (have j0 := eq23429 (σ (M.op x y))
       grind)
    | exact resolve eq23429 eq43626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23429 eq43626
  have eq43637 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq43632
  have eq43640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26 eq43637
    | exact resolve eq43637 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43637
  have eq43645 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq43640
       have r₂ := eq27
       grind)
    | exact resolve eq43640 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43640
  have eq43652 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq43645 eq31
    | exact resolve eq31 eq43645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43645
  have eq43752 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq43652
    | exact resolve eq43652 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43652
  have eq43753 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq43752
  have eq43769 : (M.op x y) = (τ (σ y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq43753 eq28
    | exact resolve eq28 eq43753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq43753
  have eq43815 : (M.op x y) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq43769
    | exact resolve eq43769 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43769
  have eq43832 : y = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq43815 eq31
    | exact resolve eq31 eq43815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43873 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq43815 eq22193
    | exact resolve eq22193 eq43815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22193
  have eq43962 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq43873
  have eq44040 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq22241 eq43832
    | exact resolve eq43832 eq22241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43832
  have eq44068 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq22241 eq44040
    | exact resolve eq44040 eq22241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44040
  have eq44105 : x = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq43962 eq29
    | exact resolve eq29 eq43962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43962
  have eq44246 : x = (τ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22241 eq44105
    | exact resolve eq44105 eq22241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44105
  have eq44279 : x = (σ y) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq44068 eq44246
    | exact resolve eq44246 eq44068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44068 eq44246
  have eq44296 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq44279
       have r₂ := eq22268
       grind)
    | exact resolve eq44279 eq22268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44279
  have eq44307 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq44296 eq26
    | exact resolve eq26 eq44296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44308 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq44296 eq31
    | exact resolve eq31 eq44296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq44473 : (σ y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq22241 eq44308
    | exact resolve eq44308 eq22241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22241 eq44308
  have eq44490 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq44296 eq44473
    | exact resolve eq44473 eq44296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44473
  have eq44565 : x = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq44307 eq31194
    | exact resolve eq31194 eq44307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31194 eq44307
  have eq44577 : x = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq44565
  have eq44586 : x = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23295 eq44577
    | exact resolve eq44577 eq23295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23295 eq44577
  have eq44593 : x = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22727 eq44586
    | exact resolve eq44586 eq22727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22727 eq44586
  have eq44596 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq44593
       have r₂ := eq22268
       grind)
    | exact resolve eq44593 eq22268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44593
  have eq44598 : (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq44296 eq44596
    | exact resolve eq44596 eq44296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44296 eq44596
  have eq44601 : x = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq44598 eq29
    | exact resolve eq29 eq44598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44598
  have eq44737 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq44490 eq44601
    | exact resolve eq44601 eq44490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44490 eq44601
  have eq44817 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq22268
       have i₂ := eq44737
       grind)
    | exact superpose eq44737 eq22268
    | exact resolve eq22268 eq44737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22268
  have eq44878 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq44817
       have r₂ := eq43815
       grind)
    | exact resolve eq44817 eq43815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43815 eq44817
  have eq44961 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq44878
  have eq44962 : x = y := by
    first
    | (have r₁ := eq44961
       have r₂ := eq44737
       grind)
    | exact resolve eq44961 eq44737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44737 eq44961
  have eq44971 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq44962
       grind)
    | exact superpose eq44962 eq18
    | exact resolve eq18 eq44962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq44972 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq44962
       grind)
    | exact superpose eq44962 eq24
    | exact resolve eq24 eq44962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq44962
  have eq44996 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq44972
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44972
    | exact resolve eq44972 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq44972
  have eq44999 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq44996 eq26
    | exact resolve eq26 eq44996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq44996
  have eq45110 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq701 x X0
       have i₂ := eq44971
       grind)
    | exact superpose eq44971 eq701
    | exact resolve eq701 eq44971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45177 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2344 X0 x
       have i₂ := eq44971
       grind)
    | exact superpose eq44971 eq2344
    | exact resolve eq2344 eq44971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344 eq44971
  have eq45394 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq45177
    | (have j0 := eq45177 X0
       grind)
    | exact resolve eq45177 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq45177
  have eq45494 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq45394 x
       have i₂ := eq45110 x
       grind)
    | exact superpose eq45110 eq45394
    | exact resolve eq45394 eq45110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45394
  have eq45785 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq44999 eq701
    | exact resolve eq701 eq44999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq44999
  have eq46119 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45785 x
       have i₂ := eq45110 x
       grind)
    | exact superpose eq45110 eq45785
    | exact resolve eq45785 eq45110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45110 eq45785
  have eq46464 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq46119 eq27
    | exact resolve eq27 eq46119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq46119
  have eq46509 : False := by grind
  exact eq46509

/-- `Equation2162`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation2162 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2162 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2162.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq58 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq58 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq58 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq253 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq260 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq253 X0 X1
       have j1 := eq62 X0 X1
       grind)
    | (have r₁ := eq253 X0 X1
       have r₂ := eq62 X0 X1
       grind)
    | (have r₁ := eq253 X0 X0
       have r₂ := eq62 X0 X0
       grind)
    | exact resolve eq253 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq253
  have eq535 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq260 (σ X1) (σ X0)
       grind)
    | exact superpose eq260 eq15
    | exact resolve eq15 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 X1
       have i₂ := eq260 X1 X0
       grind)
    | exact superpose eq260 eq535
    | exact resolve eq535 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq535
  have eq545 : False := by grind
  exact eq545

/-- `Equation2162`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation2162 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2162 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2162.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq332 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq333 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq3479 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq333 x y
       grind)
    | exact superpose eq333 eq16
    | (have j1 := eq333 x y
       grind)
    | exact resolve eq16 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3530 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq333 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq17934 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq332
    | exact resolve eq332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq18035 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17934 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq17934
    | (have j0 := eq17934 X0 X1
       grind)
    | exact resolve eq17934 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17934
  have eq32651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3479
       have i₂ := eq18035 y x
       grind)
    | exact superpose eq18035 eq3479
    | (have j1 := eq18035 (σ y) (σ x)
       grind)
    | (have r₁ := eq3479
       have r₂ := eq18035 y x
       grind)
    | (have r₁ := eq3479
       have r₂ := eq18035 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3479
       have r₂ := eq18035 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3479 eq18035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479
  have eq32652 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32651
  have eq36542 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32652
       grind)
    | exact superpose eq32652 eq16
    | exact resolve eq16 eq32652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32652
  have eq36543 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq36542
       have r₂ := eq22 x
       grind)
    | exact resolve eq36542 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36542
  have eq36546 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq36543
       grind)
    | exact superpose eq36543 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq36543
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq36543
       grind)
    | exact resolve eq13 eq36543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36543
  have eq36626 : x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq36546
  have eq53294 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36626
       grind)
    | exact superpose eq36626 eq16
    | exact resolve eq16 eq36626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36626
  have eq53295 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq53294
       have r₂ := eq22 x
       grind)
    | exact resolve eq53294 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53294
  have eq53299 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3530 x y
       have i₂ := eq53295
       grind)
    | exact superpose eq53295 eq3530
    | (have j0 := eq3530 x y
       grind)
    | exact resolve eq3530 eq53295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530 eq53295
  have eq53320 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq53299
  have eq53321 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq53320
  have eq53327 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq53321
       grind)
    | exact superpose eq53321 eq10
    | exact resolve eq10 eq53321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53321
  have eq53442 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53327
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq53327
    | exact resolve eq53327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53327
  have eq53444 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53442
       grind)
    | exact superpose eq53442 eq16
    | exact resolve eq16 eq53442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53442
  have eq53445 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq53444
       have r₂ := eq22 x
       grind)
    | exact resolve eq53444 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53444
  have eq53451 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53445
       grind)
    | exact superpose eq53445 eq16
    | exact resolve eq16 eq53445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53480 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq53445
       grind)
    | exact superpose eq53445 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq53445
       grind)
    | exact resolve eq13 eq53445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53573 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq53480
  have eq53574 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq53573
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq53573
    | exact resolve eq53573 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53573
  have eq55759 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq53445
       have i₂ := eq53574
       grind)
    | exact superpose eq53574 eq53445
    | exact resolve eq53445 eq53574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53445
  have eq55763 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq53574
       grind)
    | exact superpose eq53574 eq10
    | exact resolve eq10 eq53574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53574
  have eq55878 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq55763
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq55763
    | exact resolve eq55763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55763
  have eq55880 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq55759
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq55759
    | exact resolve eq55759 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55759
  have eq55884 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq53451
       have i₂ := eq55878
       grind)
    | exact superpose eq55878 eq53451
    | exact resolve eq53451 eq55878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55878
  have eq55889 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq55884
       have r₂ := eq55880
       grind)
    | exact resolve eq55884 eq55880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55880 eq55884
  have eq55902 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18035 y x
       have i₂ := eq55889
       grind)
    | exact superpose eq55889 eq18035
    | (have j0 := eq18035 y x
       grind)
    | exact resolve eq18035 eq55889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18035 eq55889
  have eq56020 : x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq55902
       have r₂ := eq53451
       grind)
    | exact resolve eq55902 eq53451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55902
  have eq56054 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56020
       grind)
    | exact superpose eq56020 eq16
    | exact resolve eq16 eq56020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56020
  have eq56066 : x = (M.op x y) := by
    first
    | (have r₁ := eq56054
       have r₂ := eq22 x
       grind)
    | exact resolve eq56054 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq56054
  have eq56074 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq53451
       have i₂ := eq56066
       grind)
    | exact superpose eq56066 eq53451
    | exact resolve eq53451 eq56066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53451 eq56066
  have eq56173 : False := by grind
  exact eq56173

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then Y else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_y_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq29 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq54 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq60 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq78 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq54 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y X0
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 X0 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq78 eq54
    | exact resolve eq54 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq12
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq100 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 (σ y) (σ (k y x))
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq135 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq131
    | exact resolve eq131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq101 (σ X0)
       grind)
    | exact superpose eq101 eq15
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq138 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq138
    | exact resolve eq138 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq214 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq10
    | exact resolve eq10 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 (M.op X0 X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq29
    | exact resolve eq29 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq222 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq37
    | exact resolve eq37 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq260 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq214 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq214
    | exact resolve eq214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1477 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq217 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq217
    | (have j0 := eq217 x
       grind)
    | exact resolve eq217 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1508 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1477 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq14 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1509 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1508
       have i₂ := eq54 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1508
       have i₂ := eq54 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq54 eq1508
    | exact resolve eq1508 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508
  have eq2244 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq222
    | (have j0 := eq222 (M.op x y)
       grind)
    | exact resolve eq222 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq2296 : (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2244 eq14
    | (have j0 := eq14 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2297 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2296
       have i₂ := eq54 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2296
       have i₂ := eq54 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq54 eq2296
    | exact resolve eq2296 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq5428 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X0 X1
       have i₂ := eq54 X0 X0 X0
       grind)
    | exact superpose eq54 eq95
    | (have j0 := eq95 X0 X0 X1
       grind)
    | (have r₁ := eq95 x x x
       have r₂ := eq54 x x x
       grind)
    | exact resolve eq95 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq5429 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5428 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5428
  have eq5433 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq84 eq100
    | (have r₁ := eq100 (M.op x y) y
       have r₂ := eq84 (M.op x y)
       grind)
    | exact resolve eq100 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq5434 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq81 eq100
    | (have r₁ := eq100 x (M.op x y)
       have r₂ := eq81 x
       grind)
    | exact resolve eq100 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq5440 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5434
  have eq5441 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5433
  have eq5445 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5440 eq1509
    | exact resolve eq1509 eq5440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509 eq5440
  have eq5448 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5441 eq2297
    | exact resolve eq2297 eq5441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq5449 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5441 eq2244
    | exact resolve eq2244 eq5441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244 eq5441
  have eq5451 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5445
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5445
    | exact resolve eq5445 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5445
  have eq5453 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq5449
    | exact resolve eq5449 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5449
  have eq5454 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq5448
    | exact resolve eq5448 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5448
  have eq11122 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq5451 eq54
    | exact resolve eq54 eq5451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5451
  have eq11135 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5454 eq54
    | exact resolve eq54 eq5454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq12195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11135 eq11122
    | exact resolve eq11122 eq11135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11135
  have eq12211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq12195
    | exact resolve eq12195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12195
  have eq12213 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq12211
       have r₂ := eq28
       grind)
    | exact resolve eq12211 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12211
  have eq12248 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12213 eq5429
    | exact resolve eq5429 eq12213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12213
  have eq12255 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq12248
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq12248
    | exact resolve eq12248 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12248
  have eq12932 : (τ (σ y)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12255 eq260
    | exact resolve eq260 eq12255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq12950 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq12255
  have eq12960 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq38 eq12932
    | exact resolve eq12932 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12932
  have eq12975 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq40 eq12960
    | exact resolve eq12960 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12960
  have eq13105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12975 eq5454
    | exact resolve eq5454 eq12975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5454 eq12975
  have eq13137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13105
  have eq13149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq13137
    | exact resolve eq13137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13137
  have eq13161 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13149
       have r₂ := eq28
       grind)
    | exact resolve eq13149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13149
  have eq13170 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13161 eq139
    | exact resolve eq139 eq13161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13161
  have eq13198 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq13170
    | exact resolve eq13170 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13170
  have eq13201 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13198
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13198
    | exact resolve eq13198 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13198
  have eq13250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13201 eq11122
    | exact resolve eq11122 eq13201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13277 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13250
  have eq13291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq13277
    | exact resolve eq13277 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13277
  have eq13303 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13291
       have r₂ := eq28
       grind)
    | exact resolve eq13291 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13291
  have eq13396 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13303 eq5429
    | exact resolve eq5429 eq13303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13303
  have eq13403 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13396
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq13396
    | exact resolve eq13396 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13396
  have eq13420 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13403
       have r₂ := eq12950
       grind)
    | exact resolve eq13403 eq12950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12950 eq13403
  have eq13438 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13420 eq13201
    | exact resolve eq13201 eq13420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13201
  have eq13439 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13420 eq11122
    | exact resolve eq11122 eq13420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13420
  have eq13466 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13439
  have eq13467 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13438
  have eq13493 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13467 eq27
    | exact resolve eq27 eq13467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13497 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13467 eq40
    | exact resolve eq40 eq13467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13467
  have eq13553 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq39 eq13497
    | exact resolve eq13497 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13497
  have eq13562 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq13553 eq40
    | exact resolve eq40 eq13553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13553
  have eq13609 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq13562
    | exact resolve eq13562 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13562
  have eq13617 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13609 eq39
    | exact resolve eq39 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13609
  have eq13665 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq13617
    | exact resolve eq13617 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13617
  have eq14526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13493 eq13466
    | exact resolve eq13466 eq13493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13466 eq13493
  have eq14556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14526
  have eq14573 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq14556
       have r₂ := eq28
       grind)
    | exact resolve eq14556 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14556
  have eq14584 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14573 eq40
    | exact resolve eq40 eq14573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq14573
  have eq14631 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq14584
    | exact resolve eq14584 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14584
  have eq14639 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14631 eq39
    | exact resolve eq39 eq14631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14631
  have eq14687 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq14639
    | exact resolve eq14639 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14639
  have eq14691 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14687 eq21
    | exact resolve eq21 eq14687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14692 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14687 eq78
    | exact resolve eq78 eq14687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq14718 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq14687
  have eq14719 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14691
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14691
    | exact resolve eq14691 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14691
  have eq16166 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14692 (M.op y x)
       have i₂ := eq14692 x
       grind)
    | exact superpose eq14692 eq14692
    | exact resolve eq14692 eq14692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14692
  have eq16180 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq16166
  have eq16201 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139 y
       have i₂ := eq16180
       grind)
    | exact superpose eq16180 eq139
    | exact resolve eq139 eq16180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16180
  have eq16229 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16201
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16201
    | exact resolve eq16201 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16201
  have eq16232 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14719 eq16229
    | exact resolve eq16229 eq14719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14719 eq16229
  have eq16283 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq16232
  have eq16338 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16283 eq5453
    | exact resolve eq5453 eq16283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5453
  have eq16397 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43 eq16338
    | exact resolve eq16338 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq16338
  have eq16884 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13665 eq16397
    | exact resolve eq16397 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13665 eq16397
  have eq16932 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq16884
  have eq16965 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16932
       have r₂ := eq14718
       grind)
    | exact resolve eq16932 eq14718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14718 eq16932
  have eq16968 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16965
       have i₂ := eq101 y
       grind)
    | exact superpose eq101 eq16965
    | exact resolve eq16965 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16965
  have eq16970 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16968
       have i₂ := eq139 y
       grind)
    | exact superpose eq139 eq16968
    | exact resolve eq16968 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16968
  have eq16972 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16970
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16970
    | exact resolve eq16970 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16970
  have eq17013 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16972 eq5429
    | exact resolve eq5429 eq16972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16972
  have eq17024 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17013
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq17013
    | exact resolve eq17013 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17013
  have eq17077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17024 eq11122
    | exact resolve eq11122 eq17024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11122 eq17024
  have eq17117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17077
    | exact resolve eq17077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17077
  have eq17129 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17117
       have r₂ := eq28
       grind)
    | exact resolve eq17117 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17117
  have eq35299 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17129 eq5429
    | exact resolve eq5429 eq17129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5429 eq17129
  have eq35308 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35299
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq35299
    | exact resolve eq35299 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq35299
  have eq37124 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35308 eq16283
    | exact resolve eq16283 eq35308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16283 eq35308
  have eq37190 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq37124
  have eq37221 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37190 eq39
    | exact resolve eq39 eq37190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq37190
  have eq37275 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq37221
    | exact resolve eq37221 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq37221
  have eq37276 : x = (M.op x y) := by grind
  clear eq37275
  have eq37281 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37276 eq21
    | exact resolve eq21 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq37290 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq37276 eq81
    | exact resolve eq81 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq37293 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq37276 eq96
    | exact resolve eq96 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq40764 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq37276 eq37293
    | exact resolve eq37293 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37276 eq37293
  have eq40767 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37281
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37281
    | exact resolve eq37281 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37281
  have eq41109 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq40767 eq23
    | exact resolve eq23 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq41110 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq40767 eq27
    | exact resolve eq27 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41122 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40767 eq135
    | exact resolve eq135 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq43088 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | exact superpose eq40767 eq41122
    | exact resolve eq41122 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40767 eq41122
  have eq43635 : x = (M.op x x) := by
    first
    | (have i₁ := eq37290 (M.op x x)
       have i₂ := eq37290 x
       grind)
    | exact superpose eq37290 eq37290
    | exact resolve eq37290 eq37290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37290
  have eq43783 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq40764
       have i₂ := eq43635
       grind)
    | exact superpose eq43635 eq40764
    | (have r₁ := eq40764
       have r₂ := eq43635
       grind)
    | exact resolve eq40764 eq43635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40764
  have eq43805 : x = (k y x) := by grind
  clear eq43783
  have eq43849 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43088
       have i₂ := eq43805
       grind)
    | exact superpose eq43805 eq43088
    | exact resolve eq43088 eq43805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43088 eq43805
  have eq43874 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43849
       have i₂ := eq41109
       grind)
    | exact superpose eq41109 eq43849
    | exact resolve eq43849 eq41109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43849
  have eq43875 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq43874
  have eq44056 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq139 x
       have i₂ := eq43635
       grind)
    | exact superpose eq43635 eq139
    | exact resolve eq139 eq43635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq43635
  have eq44110 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq44056
       have i₂ := eq41109
       grind)
    | exact superpose eq41109 eq44056
    | exact resolve eq44056 eq41109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41109 eq44056
  have eq44283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq44110 eq43875
    | exact resolve eq43875 eq44110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43875
  have eq44297 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq44283
       have r₂ := eq28
       grind)
    | exact resolve eq44283 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44283
  have eq45356 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq44297 eq41110
    | exact resolve eq41110 eq44297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41110 eq44297
  have eq45398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44110 eq45356
    | exact resolve eq45356 eq44110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44110 eq45356
  have eq45873 : False := by grind
  exact eq45873

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq67 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq67
    | exact resolve eq67 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq67
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq128 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq16
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq172 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq379 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq342
    | (have j0 := eq342 X0 X1
       grind)
    | exact resolve eq342 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq503 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq128
    | exact resolve eq128 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq536 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq503
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq503
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq503
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq503
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq503 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq537 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq536
  have eq2588 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq136
    | (have j0 := eq136 X0 X1
       grind)
    | exact resolve eq136 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq2589 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2588 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq2588
    | (have j0 := eq2588 X0 X1
       grind)
    | exact resolve eq2588 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2588
  have eq7380 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq537
       grind)
    | exact superpose eq537 eq16
    | exact resolve eq16 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq7381 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7380
       have r₂ := eq77 x
       grind)
    | exact resolve eq7380 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7380
  have eq743065 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq7381
       grind)
    | exact superpose eq7381 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7381
       grind)
    | exact resolve eq12 eq7381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7381
  have eq743657 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq743065
  have eq795482 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2589 x y
       have i₂ := eq743657
       grind)
    | exact superpose eq743657 eq2589
    | (have j0 := eq2589 x y
       grind)
    | exact resolve eq2589 eq743657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2589 eq743657
  have eq795735 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq795482
  have eq795736 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq795735
  have eq796480 : y = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq795736
       grind)
    | exact superpose eq795736 eq10
    | exact resolve eq10 eq795736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795736
  have eq797248 : x = y ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq796480
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq796480
    | exact resolve eq796480 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796480
  have eq798265 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq797248
       grind)
    | exact superpose eq797248 eq16
    | exact resolve eq16 eq797248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797248
  have eq798266 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq798265
       have r₂ := eq77 x
       grind)
    | exact resolve eq798265 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq798265
  have eq800055 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq798266
       grind)
    | exact superpose eq798266 eq16
    | exact resolve eq16 eq798266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800063 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq172 x (σ y)
       have i₂ := eq798266
       grind)
    | exact superpose eq798266 eq172
    | (have j0 := eq172 x (σ y)
       grind)
    | (have r₁ := eq172 x (σ y)
       have r₂ := eq798266
       grind)
    | exact resolve eq172 eq798266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq798266
  have eq800864 : (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq800063
  have eq800913 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq800864
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq800864
    | exact resolve eq800864 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800864
  have eq803638 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq379 y x
       have i₂ := eq800913
       grind)
    | exact superpose eq800913 eq379
    | (have j0 := eq379 (σ (M.op x y)) (σ (M.op x x))
       grind)
    | exact resolve eq379 eq800913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq800913
  have eq804566 : x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq803638
       have r₂ := eq800055
       grind)
    | exact resolve eq803638 eq800055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803638
  have eq810106 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq800055
       have i₂ := eq804566
       grind)
    | exact superpose eq804566 eq800055
    | exact resolve eq800055 eq804566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804566
  have eq810109 : (M.op x y) = (M.op x x) := by grind
  clear eq810106
  have eq811124 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq800055
       have i₂ := eq810109
       grind)
    | exact superpose eq810109 eq800055
    | exact resolve eq800055 eq810109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800055 eq810109
  have eq811726 : False := by grind
  exact eq811726

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_y_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  clear eq23
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op (M.op X1 X0) (M.op X1 X2))) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op (M.op X1 X0) (M.op X1 X2))) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq521 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq530 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq521 X0
       grind)
    | exact superpose eq521 eq14
    | exact resolve eq14 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  clear eq68
  have eq878 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq869 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq913 : ∀ X0 X1 : G, (k (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq878 X1 (M.op X0 X0) X0
       have i₂ := eq521 X0
       grind)
    | exact superpose eq521 eq878
    | exact resolve eq878 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq878
  have eq1052 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq530
    | exact resolve eq530 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq1570 : (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq50 eq913
    | exact resolve eq913 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1573 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq913
    | exact resolve eq913 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq913
  have eq1584 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1570 eq46
    | exact resolve eq46 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq1570
  have eq1588 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq1584
    | exact resolve eq1584 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1584
  have eq1595 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1588 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1596 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1595
  have eq1721 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1596 eq1052
    | exact resolve eq1052 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1724 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1721
  have eq18261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18268 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18261
    | exact resolve eq18261 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18261
  have eq18279 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq18268
       have r₂ := eq28
       grind)
    | exact resolve eq18268 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18268
  have eq18282 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18279
    | exact resolve eq18279 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18279
  have eq18433 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18282 eq1052
    | exact resolve eq1052 eq18282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18282
  have eq18437 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18433
    | exact resolve eq18433 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18433
  have eq18438 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18437
  have eq18505 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1052 x x
       have i₂ := eq18438
       grind)
    | exact superpose eq18438 eq1052
    | exact resolve eq1052 eq18438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18438
  have eq18509 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18505
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18505
    | exact resolve eq18505 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18505
  have eq18510 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18509
  have eq18513 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18510 eq28
    | exact resolve eq28 eq18510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18559 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18510 eq1573
    | exact resolve eq1573 eq18510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573 eq18510
  have eq18663 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18559 eq88
    | exact resolve eq88 eq18559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq18559
  have eq18679 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq18663
  have eq18689 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18679
       have r₂ := eq18513
       grind)
    | exact resolve eq18679 eq18513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18513 eq18679
  have eq18761 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1052 x x
       have i₂ := eq18689
       grind)
    | exact superpose eq18689 eq1052
    | exact resolve eq1052 eq18689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq18689
  have eq18765 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18761
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18761
    | exact resolve eq18761 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq18761
  have eq18766 : y = (M.op x y) := by grind
  clear eq18765
  have eq18851 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq18766 eq21
    | exact resolve eq21 eq18766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18766
  have eq18992 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18851
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18851
    | exact resolve eq18851 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18851
  have eq18994 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq18992 eq27
    | exact resolve eq27 eq18992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18992
  have eq19132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1724 eq18994
    | exact resolve eq18994 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724 eq18994
  have eq19142 : False := by grind
  exact eq19142

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then Y else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_y_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq51 : y ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq464 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq649 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq23192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq23192
    | exact resolve eq23192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23192
  have eq23213 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq23202
       have r₂ := eq28
       grind)
    | exact resolve eq23202 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23202
  have eq23216 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq23213
    | exact resolve eq23213 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23213
  have eq23372 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23216 eq464
    | exact resolve eq464 eq23216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23216
  have eq23425 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq23372
    | exact resolve eq23372 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23372
  have eq23426 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23425
  have eq23431 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq464 y
       have i₂ := eq23426
       grind)
    | exact superpose eq23426 eq464
    | exact resolve eq464 eq23426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23432 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71 y
       have i₂ := eq23426
       grind)
    | exact superpose eq23426 eq71
    | exact resolve eq71 eq23426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq23426
  have eq23483 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23432
       have r₂ := eq51
       grind)
    | exact resolve eq23432 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq23432
  have eq23484 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23431
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23431
    | exact resolve eq23431 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23431
  have eq23485 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23484
  have eq23486 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23485 eq28
    | exact resolve eq28 eq23485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23485
  have eq23667 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq23483
       grind)
    | exact superpose eq23483 eq45
    | exact resolve eq45 eq23483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq23683 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq649 x y
       have i₂ := eq23483
       grind)
    | exact superpose eq23483 eq649
    | (have j0 := eq649 x y
       grind)
    | exact resolve eq649 eq23483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq23483
  have eq23684 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23683
  have eq23687 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23684
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23684
    | exact resolve eq23684 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23684
  have eq23703 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23667
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23667
    | exact resolve eq23667 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23667
  have eq23705 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23687
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23687
    | exact resolve eq23687 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23687
  have eq23714 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq23703
       have r₂ := eq52
       grind)
    | exact resolve eq23703 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq23703
  have eq23715 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23705
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23705
    | exact resolve eq23705 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23705
  have eq23724 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23715
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23715
    | exact resolve eq23715 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq23715
  have eq23733 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq23724
    | exact resolve eq23724 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23724
  have eq23734 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23733
  have eq23772 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23714 eq98
    | exact resolve eq98 eq23714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq23714
  have eq23799 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq23772
       have r₂ := eq23486
       grind)
    | exact resolve eq23772 eq23486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23486 eq23772
  have eq24192 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23734 eq464
    | exact resolve eq464 eq23734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23734
  have eq24244 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq24192
    | exact resolve eq24192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq24192
  have eq24245 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24244
  have eq24246 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq24245 eq28
    | exact resolve eq28 eq24245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24245
  have eq24991 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq464 y
       have i₂ := eq23799
       grind)
    | exact superpose eq23799 eq464
    | exact resolve eq464 eq23799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq23799
  have eq25043 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24991
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24991
    | exact resolve eq24991 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24991
  have eq25044 : y = (M.op x y) := by grind
  clear eq25043
  have eq25046 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq25044 eq21
    | exact resolve eq21 eq25044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25044
  have eq25184 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25046
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25046
    | exact resolve eq25046 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq25046
  have eq25188 : False := by grind
  exact eq25188
