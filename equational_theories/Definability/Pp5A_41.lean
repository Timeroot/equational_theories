import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq45 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op X1 (M.op X2 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq20 X0
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op X1 (M.op X2 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq45 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq47 X0
       have j1 := eq28 X0
       grind)
    | (have r₁ := eq47 X0
       have r₂ := eq28 X0
       grind)
    | exact resolve eq47 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq47
  have eq50 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq48 X0 X1 X2
       have j1 := eq27 X0 X1 X2
       grind)
    | (have r₁ := eq48 X0 X1 X2
       have r₂ := eq27 X0 X1 X2
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq48
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq87 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq50
    | exact resolve eq50 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (M.op X1 (M.op X2 (M.op (σ X0) (σ X0))))
       have i₂ := eq50 (σ X0) X1 X2
       grind)
    | exact superpose eq50 eq34
    | exact resolve eq34 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq98 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 X2 : G, (M.op X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) = X0 ∨ (M.op X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) = X0 ∨ (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0))))) = (M.op X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))
       have i₂ := eq98 X0 X1 X2
       grind)
    | exact superpose eq98 eq14
    | (have j0 := eq14 X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))
       grind)
    | exact resolve eq14 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0))))) = (M.op X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) ∨ (M.op X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq154 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq191 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq195 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ x)
       have i₂ := eq70 x x
       grind)
    | exact superpose eq70 eq20
    | (have j1 := eq70 X0 X0
       grind)
    | exact resolve eq20 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq203 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq209 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq195 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq221 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (M.op X0 (σ X1)) (σ X2)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X0 X1 X2
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq370 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq209 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq209
    | exact resolve eq209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq385 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq370 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq370
    | (have j0 := eq370 X0
       grind)
    | exact resolve eq370 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq389 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq385 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq385
    | (have j0 := eq385 X0
       grind)
    | exact resolve eq385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq411 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (k X0 X0) X0
       have i₂ := eq389 X0
       grind)
    | exact superpose eq389 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq389 X0
       grind)
    | (have r₁ := eq13 (k X0 X0) X0
       have r₂ := eq389 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq389 X0
       grind)
    | exact resolve eq13 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (k X0 X0) X0
       have i₂ := eq389 X0
       grind)
    | exact superpose eq389 eq12
    | (have j1 := eq389 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq389 X0
       grind)
    | exact resolve eq12 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq413 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq411 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq415 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq413 X0
       have j1 := eq412 X0
       grind)
    | (have r₁ := eq413 X0
       have r₂ := eq412 X0
       grind)
    | exact resolve eq413 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq413
  have eq1034 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X1))) ≠ (σ (M.op X0 (M.op X1 X1))) ∨ (σ (M.op X0 (M.op X1 X1))) = (M.op (σ (M.op X0 (M.op X1 X1))) (σ (M.op X2 X1))) ∨ (σ (M.op X2 X1)) = (M.op (σ (M.op X0 (M.op X1 X1))) (σ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq203 (M.op X0 (M.op X1 X1)) (M.op X2 X1)
       have i₂ := eq87 X1 X0 X2
       grind)
    | exact superpose eq87 eq203
    | (have j0 := eq203 (M.op X0 (M.op X1 X1)) (M.op X2 X1)
       grind)
    | exact resolve eq203 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq1051 : ∀ X0 X1 X2 : G, (σ (M.op X2 X1)) = (M.op (σ (M.op X0 (M.op X1 X1))) (σ (M.op X2 X1))) ∨ (σ (M.op X0 (M.op X1 X1))) = (M.op (σ (M.op X0 (M.op X1 X1))) (σ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1034 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1162 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq204 (τ X0) (τ X1)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq204
    | (have j0 := eq204 (τ X0) (τ X1)
       grind)
    | exact resolve eq204 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1162 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1162
    | (have j0 := eq1162 X0 X1
       grind)
    | exact resolve eq1162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1178 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1172 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1172
    | (have j0 := eq1172 X0 X1
       grind)
    | exact resolve eq1172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1182 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1178 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1178
    | (have j0 := eq1178 X0 X1
       grind)
    | exact resolve eq1178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1184 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq1185 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1184 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1184
    | (have j0 := eq1184 X0 X1
       grind)
    | exact resolve eq1184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1186 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1185 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1185
    | (have j0 := eq1185 X0 X1
       grind)
    | exact resolve eq1185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1314 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq104 x X2 X0 X1
       grind)
    | exact superpose eq104 eq50
    | exact resolve eq50 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1315 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq104 x X2 X0 X1
       grind)
    | exact superpose eq104 eq9
    | exact resolve eq9 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq1394 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1315 x X1 X0
       grind)
    | exact superpose eq1315 eq9
    | exact resolve eq9 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1400 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq1315 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1315 eq9
    | exact resolve eq9 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1401 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1314 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq1315 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1315 eq1314
    | exact resolve eq1314 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1410 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq191
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq191
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq191 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq1411 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1410
  have eq1480 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (M.op X0 (σ X1)) X1
       have i₂ := eq1401 (σ X1) X0
       grind)
    | exact superpose eq1401 eq26
    | exact resolve eq26 eq1401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1401
  have eq5611 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1315 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1400 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1400 eq1315
    | exact resolve eq1315 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315 eq1400
  have eq5684 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 X0
       have i₂ := eq5611 X1 X2 X0
       grind)
    | exact superpose eq5611 eq9
    | exact resolve eq9 eq5611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5685 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X0 (M.op X1 X2)) X2 X2
       have i₂ := eq5611 X0 X1 X2
       grind)
    | exact superpose eq5611 eq19
    | exact resolve eq19 eq5611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5611
  have eq14563 : y ≠ y ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1411
       grind)
    | exact superpose eq1411 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq1411
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1411
       grind)
    | exact resolve eq12 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq14601 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14563
  have eq18625 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq49 (σ X0)
       have i₂ := eq221 (σ X0) X0 X0
       grind)
    | exact superpose eq221 eq49
    | (have j1 := eq221 (σ X0) X0 x
       grind)
    | exact resolve eq49 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq221
  have eq18651 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18625 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18625
  have eq18659 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq18651 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18651
    | (have j0 := eq18651 X0
       grind)
    | exact resolve eq18651 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18651
  have eq18902 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq18659 (τ X0)
       grind)
    | exact superpose eq18659 eq18
    | (have j1 := eq18659 (τ X0)
       grind)
    | exact resolve eq18 eq18659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18659
  have eq18977 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18902 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq18902
    | (have j0 := eq18902 X0
       grind)
    | exact resolve eq18902 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18902
  have eq18992 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18977 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18977
    | (have j0 := eq18977 X0
       grind)
    | exact resolve eq18977 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18977
  have eq19003 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18992 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18992
    | (have j0 := eq18992 X0
       grind)
    | exact resolve eq18992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18992
  have eq19178 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq415 X0
       have i₂ := eq19003 X0
       grind)
    | exact superpose eq19003 eq415
    | (have j0 := eq415 X0
       have j1 := eq19003 X0
       grind)
    | exact resolve eq415 eq19003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq19003
  have eq19242 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19178
  have eq19287 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq19242 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq19242 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq19242 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19242
  have eq19441 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq19287 (σ X0)
       grind)
    | exact superpose eq19287 eq15
    | exact resolve eq15 eq19287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19451 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq19287 (τ X0)
       grind)
    | exact superpose eq19287 eq37
    | exact resolve eq37 eq19287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq19506 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19451 X0
       have i₂ := eq19287 X0
       grind)
    | exact superpose eq19287 eq19451
    | exact resolve eq19451 eq19287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19451
  have eq19514 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19441 X0
       have i₂ := eq19287 X0
       grind)
    | exact superpose eq19287 eq19441
    | exact resolve eq19441 eq19287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19287 eq19441
  have eq19940 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (τ X0))) = (M.op (M.op X1 (M.op X2 (τ X0))) (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5684 (τ X0) X1 X2 (τ X0)
       have i₂ := eq19506 X0
       grind)
    | exact superpose eq19506 eq5684
    | exact resolve eq5684 eq19506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5684
  have eq19941 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ X0) (M.op X1 (M.op X2 (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5685 (τ X0) X2 (τ X0) X1
       have i₂ := eq19506 X0
       grind)
    | exact superpose eq19506 eq5685
    | exact resolve eq5685 eq19506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19506
  have eq20131 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1394 (σ X0) (σ X0)
       have i₂ := eq19514 X0
       grind)
    | exact superpose eq19514 eq1394
    | exact resolve eq1394 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq20141 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5685 (σ X0) X2 (σ X0) X1
       have i₂ := eq19514 X0
       grind)
    | exact superpose eq19514 eq5685
    | exact resolve eq5685 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23707 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq20141 X0 X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq20131 (M.op X0 X0)
       grind)
    | exact superpose eq20131 eq20141
    | exact resolve eq20141 eq20131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20131 eq20141
  have eq67667 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (k (σ (M.op X2 (M.op X1 X1))) (σ (M.op X0 X1))) ∨ (σ (M.op X2 (M.op X1 X1))) = (M.op (σ (M.op X2 (M.op X1 X1))) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ (M.op X0 (M.op X1 X1))) (σ (M.op X2 X1))
       have i₂ := eq1051 X0 X1 X2
       grind)
    | exact superpose eq1051 eq12
    | (have j1 := eq1051 X2 X1 X0
       grind)
    | (have r₁ := eq12 (σ (M.op X0 (M.op X1 X1))) (σ (M.op X2 X1))
       have r₂ := eq1051 X0 X1 X2
       grind)
    | exact resolve eq12 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67708 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X1))) ≠ (σ (M.op X2 X1)) ∨ (σ (M.op X0 (M.op X1 X1))) = (M.op (σ (M.op X0 (M.op X1 X1))) (σ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1051 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq67709 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (σ (M.op X2 (M.op X1 X1))) (σ (M.op X0 X1))) ∨ (σ (M.op X2 (M.op X1 X1))) = (M.op (σ (M.op X2 (M.op X1 X1))) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq67667 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67667
  have eq67719 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (σ (k (M.op X2 (M.op X1 X1)) (M.op X0 X1))) ∨ (σ (M.op X2 (M.op X1 X1))) = (M.op (σ (M.op X2 (M.op X1 X1))) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67709 X0 X1 X2
       have i₂ := eq15 (M.op X2 (M.op X1 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq15 eq67709
    | (have j0 := eq67709 X0 X1 X2
       grind)
    | exact resolve eq67709 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67709
  have eq67802 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (σ (M.op X2 (M.op X1 X1))) ∨ (σ (M.op X2 (M.op X1 X1))) = (M.op (σ (M.op X2 (M.op X1 X1))) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67719 X0 X1 X2
       have i₂ := eq87 X1 X2 X0
       grind)
    | exact superpose eq87 eq67719
    | (have j0 := eq67719 X0 X1 X2
       grind)
    | exact resolve eq67719 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq67719
  have eq67864 : ∀ X0 X1 X2 : G, (σ (M.op X2 (M.op X1 X1))) = (M.op (σ (M.op X2 (M.op X1 X1))) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq67802 X0 X1 X2
       have j1 := eq67708 X2 X1 X0
       grind)
    | (have r₁ := eq67802 X2 X1 X0
       have r₂ := eq67708 X0 X1 X2
       grind)
    | exact resolve eq67802 eq67708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67708 eq67802
  have eq68014 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (M.op X2 (M.op X1 (τ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67864 X0 (M.op X2 (τ (M.op X0 X0))) (τ X0)
       have i₂ := eq19941 X0 (M.op X2 (τ (M.op X0 X0))) X2
       grind)
    | exact superpose eq19941 eq67864
    | exact resolve eq67864 eq19941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19941 eq67864
  have eq68269 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op X2 (M.op X1 (τ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68014 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68014
    | exact resolve eq68014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68014
  have eq69276 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (M.op X3 (M.op X0 (M.op X1 (τ X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq68269 X2 (M.op X0 (M.op X1 (τ X2))) X3
       have i₂ := eq19940 X2 X0 X1
       grind)
    | exact superpose eq19940 eq68269
    | exact resolve eq68269 eq19940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19940 eq68269
  have eq70415 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = (M.op (σ (M.op X1 (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23707 (M.op X1 (τ X0)) X0
       have i₂ := eq69276 (M.op X1 (τ X0)) X1 X0 (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0)))
       grind)
    | exact superpose eq69276 eq23707
    | exact resolve eq23707 eq69276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23707 eq69276
  have eq74023 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70415 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70415
    | exact resolve eq70415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74159 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (σ (M.op X0 (τ (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5685 X2 (σ (M.op X0 (τ (M.op X1 X2)))) X1 X3
       have i₂ := eq70415 (M.op X1 X2) X0
       grind)
    | exact superpose eq70415 eq5685
    | exact resolve eq5685 eq70415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5685 eq70415
  have eq533309 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq204 x y
       have i₂ := eq14601
       grind)
    | exact superpose eq14601 eq204
    | (have j0 := eq204 x y
       grind)
    | exact resolve eq204 eq14601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq14601
  have eq533338 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq533309
  have eq533339 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq533338
  have eq2819441 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74023 y x
       have i₂ := eq533339
       grind)
    | exact superpose eq533339 eq74023
    | exact resolve eq74023 eq533339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533339
  have eq2819789 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2819441
  have eq2821733 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2819789
       grind)
    | exact superpose eq2819789 eq16
    | exact resolve eq16 eq2819789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2821872 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq2819789
       grind)
    | exact superpose eq2819789 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2819789
       grind)
    | exact resolve eq12 eq2819789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2819789
  have eq2822317 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2821872
  have eq2822526 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq2822317
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2822317
    | exact resolve eq2822317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822317
  have eq2856347 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2822526
       grind)
    | exact superpose eq2822526 eq16
    | exact resolve eq16 eq2822526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3166541 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2))))) ≠ (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2))))) ∨ (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2))))) = (k X2 (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2)))))) ∨ (M.op X2 (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))
       have i₂ := eq158 X0 X1 X2
       grind)
    | exact superpose eq158 eq12
    | (have j1 := eq158 X2 X0 X1
       grind)
    | (have r₁ := eq12 X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))
       have r₂ := eq158 X0 X1 X2
       grind)
    | exact resolve eq12 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3166988 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0))))) ≠ X0 ∨ (M.op X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq158 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq3166989 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2))))) = (k X2 (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2)))))) ∨ (M.op X2 (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3166541 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3166541
  have eq3166991 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X2 (σ (M.op X0 X0))))) ≠ X0 ∨ (M.op X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3166988 X0 X1 X2
       have i₂ := eq19514 X0
       grind)
    | exact superpose eq19514 eq3166988
    | (have j0 := eq3166988 X0 X1 X2
       grind)
    | exact resolve eq3166988 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3166988
  have eq3167438 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2))))) = X2 ∨ (M.op X2 (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3166989 X0 X1 X2
       have i₂ := eq98 X2 X0 X1
       grind)
    | exact superpose eq98 eq3166989
    | (have j0 := eq3166989 X0 X1 X2
       grind)
    | exact resolve eq3166989 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq3166989
  have eq3167872 : ∀ X0 X1 X2 : G, (M.op X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 ∨ (τ (M.op X1 (M.op X2 (σ (M.op X0 X0))))) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3166991 X0 X1 X2
       have i₂ := eq19514 X0
       grind)
    | exact superpose eq19514 eq3166991
    | (have j0 := eq3166991 X0 X1 X2
       grind)
    | exact resolve eq3166991 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3166991
  have eq3168319 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 (σ (M.op X2 X2))))) = X2 ∨ (M.op X2 (τ (M.op X0 (M.op X1 (M.op (σ X2) (σ X2)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3167438 X0 X1 X2
       have i₂ := eq19514 X2
       grind)
    | exact superpose eq19514 eq3167438
    | (have j0 := eq3167438 X0 X1 X2
       grind)
    | exact resolve eq3167438 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167438
  have eq3169017 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op X1 (σ (M.op X2 X2)))))) = X2 ∨ (τ (M.op X0 (M.op X1 (σ (M.op X2 X2))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3168319 X0 X1 X2
       have i₂ := eq19514 X2
       grind)
    | exact superpose eq19514 eq3168319
    | (have j0 := eq3168319 X0 X1 X2
       grind)
    | exact resolve eq3168319 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168319
  have eq3169301 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op X1 (σ (M.op X2 X2)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3169017 X0 X1 X2
       have j1 := eq3167872 X2 X0 X1
       grind)
    | (have r₁ := eq3169017 X1 X2 X0
       have r₂ := eq3167872 X0 X1 X2
       grind)
    | exact resolve eq3169017 eq3167872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167872 eq3169017
  have eq3169756 : ∀ X0 X1 : G, (τ (M.op X1 X0)) = (M.op (τ (M.op X1 X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3169301 X0 x (τ (M.op X1 X0))
       have i₂ := eq74159 (τ (M.op X1 X0)) X1 X0 x
       grind)
    | exact superpose eq74159 eq3169301
    | exact resolve eq3169301 eq74159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74159 eq3169301
  have eq3184415 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq3169756 (σ y) (σ x)
       have i₂ := eq2822526
       grind)
    | exact superpose eq2822526 eq3169756
    | exact resolve eq3169756 eq2822526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822526 eq3169756
  have eq3187223 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq3184415
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3184415
    | exact resolve eq3184415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3184415
  have eq3187773 : x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq3187223
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3187223
    | exact resolve eq3187223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187223
  have eq3188072 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq2856347
       have i₂ := eq3187773
       grind)
    | exact superpose eq3187773 eq2856347
    | exact resolve eq2856347 eq3187773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856347 eq3187773
  have eq3188566 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq3188072
  have eq3188567 : (σ y) = (σ (k x y)) := by grind
  clear eq3188566
  have eq3190296 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq3188567
       grind)
    | exact superpose eq3188567 eq10
    | exact resolve eq10 eq3188567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3188567
  have eq3191320 : y = (k x y) := by
    first
    | (have i₁ := eq3190296
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3190296
    | exact resolve eq3190296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3190296
  have eq3191442 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1186 x y
       have i₂ := eq3191320
       grind)
    | exact superpose eq3191320 eq1186
    | (have j0 := eq1186 x y
       grind)
    | (have r₁ := eq1186 x y
       have r₂ := eq3191320
       grind)
    | exact resolve eq1186 eq3191320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq3191473 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3191442
  have eq3199452 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2821733
       have i₂ := eq3191473
       grind)
    | exact superpose eq3191473 eq2821733
    | exact resolve eq2821733 eq3191473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821733 eq3191473
  have eq3199951 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3199452
  have eq3291306 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74023 y x
       have i₂ := eq3199951
       grind)
    | exact superpose eq3199951 eq74023
    | exact resolve eq74023 eq3199951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74023 eq3199951
  have eq3291658 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3291306
  have eq3295040 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq1480 (σ x) y
       have i₂ := eq3291658
       grind)
    | exact superpose eq3291658 eq1480
    | exact resolve eq1480 eq3291658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480 eq3291658
  have eq3295906 : x = (k x y) := by
    first
    | (have i₁ := eq3295040
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3295040
    | exact resolve eq3295040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295040
  have eq3298498 : x = y := by
    first
    | (have i₁ := eq3191320
       have i₂ := eq3295906
       grind)
    | exact superpose eq3295906 eq3191320
    | exact resolve eq3191320 eq3295906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191320 eq3295906
  have eq3298546 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3298498
       grind)
    | exact superpose eq3298498 eq16
    | exact resolve eq16 eq3298498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298498
  have eq3298750 : False := by grind
  exact eq3298750

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
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
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq55 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq187 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq194 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       have j1 := eq59 X1 X0
       grind)
    | (have r₁ := eq187 X1 X0
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq187 X0 X0
       have r₂ := eq59 X0 X0
       grind)
    | exact resolve eq187 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq187
  have eq419 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq194 (σ X0) (σ X1)
       grind)
    | exact superpose eq194 eq15
    | exact resolve eq15 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq194 X0 X1
       grind)
    | exact superpose eq194 eq419
    | exact resolve eq419 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq419
  have eq429 : False := by grind
  exact eq429

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq29 (σ X0)
       grind)
    | exact superpose eq29 eq15
    | exact resolve eq15 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq29 (τ X0)
       grind)
    | exact superpose eq29 eq18
    | exact resolve eq18 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq31
    | exact resolve eq31 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq33
    | exact resolve eq33 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq33
  have eq70 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq21
    | exact resolve eq21 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq82 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq80
    | (have j0 := eq80 X0 X1
       grind)
    | exact resolve eq80 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq82
  have eq125 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq197 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq225 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq197
    | (have j0 := eq197 X0 X1
       grind)
    | exact resolve eq197 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq232 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq225 X0 X1
       have j1 := eq70 X1 X0
       grind)
    | (have r₁ := eq225 (M.op (σ X0) X1) X0
       have r₂ := eq70 X0 X1
       grind)
    | (have r₁ := eq225 X1 X0
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq225 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq225
  have eq436 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq232
    | (have j0 := eq232 X1 (τ X0)
       grind)
    | exact resolve eq232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq232 (σ X0) X1
       grind)
    | exact superpose eq232 eq15
    | (have j1 := eq232 (σ X0) X1
       grind)
    | exact resolve eq15 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq461 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq436
    | (have j0 := eq436 X0 X1
       grind)
    | exact resolve eq436 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq436
  have eq479 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq461 X1 (τ X0)
       grind)
    | exact superpose eq461 eq18
    | (have j1 := eq461 X1 (τ X0)
       grind)
    | exact resolve eq18 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq461
  have eq836 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq125 x X2 X0 X1
       grind)
    | exact superpose eq125 eq9
    | exact resolve eq9 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq870 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq836 x X1 X0
       grind)
    | exact superpose eq836 eq9
    | exact resolve eq9 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq1363 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq479 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq479
    | exact resolve eq479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq1438 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1363 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1363
    | (have j0 := eq1363 X0 X1
       grind)
    | exact resolve eq1363 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1891 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq448 x y
       grind)
    | exact superpose eq448 eq16
    | (have j1 := eq448 x y
       grind)
    | exact resolve eq16 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq2080 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1891
       have i₂ := eq1438 x y
       grind)
    | exact superpose eq1438 eq1891
    | (have j1 := eq1438 x y
       grind)
    | (have r₁ := eq1891
       have r₂ := eq1438 x y
       grind)
    | exact resolve eq1891 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438 eq1891
  have eq2081 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2080
  have eq2090 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq71 y
       have i₂ := eq2081
       grind)
    | exact superpose eq2081 eq71
    | exact resolve eq71 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2101 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq870 y y
       have i₂ := eq2081
       grind)
    | exact superpose eq2081 eq870
    | exact resolve eq870 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq2185 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2090
       grind)
    | exact superpose eq2090 eq16
    | exact resolve eq16 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2326 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2185
       have i₂ := eq2101
       grind)
    | exact superpose eq2101 eq2185
    | exact resolve eq2185 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101 eq2185
  have eq2327 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2326
  have eq2328 : (σ x) = (σ (M.op y y)) := by grind
  clear eq2327
  have eq2435 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71 y
       have i₂ := eq2328
       grind)
    | exact superpose eq2328 eq71
    | exact resolve eq71 eq2328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2436 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2328
       grind)
    | exact superpose eq2328 eq10
    | exact resolve eq10 eq2328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328
  have eq2482 : x = (M.op y y) := by
    first
    | (have i₁ := eq2436
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2436
    | exact resolve eq2436 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436
  have eq2501 : x = (M.op x y) := by
    first
    | (have i₁ := eq870 y y
       have i₂ := eq2482
       grind)
    | exact superpose eq2482 eq870
    | exact resolve eq870 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq2482
  have eq2606 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2435
       grind)
    | exact superpose eq2435 eq16
    | exact resolve eq16 eq2435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435
  have eq2621 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2606
       have i₂ := eq2501
       grind)
    | exact superpose eq2501 eq2606
    | exact resolve eq2606 eq2501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501 eq2606
  have eq2622 : False := by grind
  exact eq2622

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq46 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq46 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq47 (σ X0)
       grind)
    | exact superpose eq47 eq15
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq47 (τ X0)
       grind)
    | exact superpose eq47 eq18
    | exact resolve eq18 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq51 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51
    | exact resolve eq51 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq59 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq54
    | exact resolve eq54 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq54
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq233 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq199
  have eq237 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq233 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq233 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq233 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq240 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq237
    | (have j0 := eq237 X0 X1
       grind)
    | exact resolve eq237 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq237
  have eq584 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq240
    | exact resolve eq240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq240 (σ X0) X1
       grind)
    | exact superpose eq240 eq15
    | (have j1 := eq240 (σ X0) X1
       grind)
    | exact resolve eq15 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq611 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq596 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq596
    | (have j0 := eq596 X0 X1
       grind)
    | exact resolve eq596 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq596
  have eq628 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq584 (τ X1) X0
       grind)
    | exact superpose eq584 eq18
    | (have j1 := eq584 (τ X1) X0
       grind)
    | exact resolve eq18 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq584
  have eq1635 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq628
    | exact resolve eq628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq1693 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1635 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1635
    | (have j0 := eq1635 X0 X1
       grind)
    | exact resolve eq1635 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq6709 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq611 x y
       grind)
    | exact superpose eq611 eq16
    | (have j1 := eq611 x y
       grind)
    | exact resolve eq16 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6782 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq611 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq6981 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq6709
       have i₂ := eq1693 y x
       grind)
    | exact superpose eq1693 eq6709
    | (have j1 := eq1693 y x
       grind)
    | (have r₁ := eq6709
       have r₂ := eq1693 y x
       grind)
    | exact resolve eq6709 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6982 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6981
  have eq6986 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq6982
       grind)
    | exact superpose eq6982 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6982
       grind)
    | exact resolve eq13 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6982
  have eq7006 : (k x y) = (M.op x x) ∨ x = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6986
  have eq69818 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6782 x y
       have i₂ := eq7006
       grind)
    | exact superpose eq7006 eq6782
    | (have j0 := eq6782 x y
       grind)
    | exact resolve eq6782 eq7006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6782 eq7006
  have eq69832 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y x) := by grind
  clear eq69818
  have eq69833 : x = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq69832
  have eq70314 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq69833
       grind)
    | exact superpose eq69833 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq69833
       grind)
    | exact resolve eq12 eq69833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69833
  have eq70356 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq70314
  have eq70858 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6709
       have i₂ := eq70356
       grind)
    | exact superpose eq70356 eq6709
    | exact resolve eq6709 eq70356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6709 eq70356
  have eq70883 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq70858
  have eq70884 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq70883
  have eq71408 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70884
       grind)
    | exact superpose eq70884 eq16
    | exact resolve eq16 eq70884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71409 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq90 x (σ y)
       have i₂ := eq70884
       grind)
    | exact superpose eq70884 eq90
    | (have j0 := eq90 x (σ y)
       grind)
    | (have r₁ := eq90 x (σ y)
       have r₂ := eq70884
       grind)
    | exact resolve eq90 eq70884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq71475 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq71409
  have eq71493 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq71475
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq71475
    | exact resolve eq71475 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71475
  have eq77296 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq71493
       grind)
    | exact superpose eq71493 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq71493
       grind)
    | exact resolve eq12 eq71493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71493
  have eq77338 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq77296
  have eq77357 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq77338
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq77338
    | exact resolve eq77338 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77338
  have eq77394 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq77357
       have i₂ := eq70884
       grind)
    | exact superpose eq70884 eq77357
    | exact resolve eq77357 eq70884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70884 eq77357
  have eq77395 : (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq77394
  have eq77427 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1693 y x
       have i₂ := eq77395
       grind)
    | exact superpose eq77395 eq1693
    | (have j0 := eq1693 y x
       grind)
    | exact resolve eq1693 eq77395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693 eq77395
  have eq77596 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq77427
       have r₂ := eq71408
       grind)
    | exact resolve eq77427 eq71408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77427
  have eq78211 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq71408
       have i₂ := eq77596
       grind)
    | exact superpose eq77596 eq71408
    | exact resolve eq71408 eq77596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71408 eq77596
  have eq78257 : False := by grind
  exact eq78257

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq71 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq68
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108
    | exact resolve eq108 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq626 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq9864 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9864
    | exact resolve eq9864 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9864
  have eq9876 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq9865
       have r₂ := eq28
       grind)
    | exact resolve eq9865 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9865
  have eq9878 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9876
    | exact resolve eq9876 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9876
  have eq9881 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9878
  have eq9893 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9881
    | exact resolve eq9881 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9881
  have eq10013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9893 eq109
    | exact resolve eq109 eq9893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9893
  have eq10023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10013
  have eq10025 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10023
       have r₂ := eq28
       grind)
    | exact resolve eq10023 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10023
  have eq10140 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10025
  have eq10152 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10140
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10140
    | exact resolve eq10140 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10140
  have eq10269 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq10152
       grind)
    | exact superpose eq10152 eq68
    | exact resolve eq68 eq10152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10152
  have eq10287 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10269
    | exact resolve eq10269 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10269
  have eq10316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10287 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10316
    | exact resolve eq10316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10316
  have eq10330 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10319
       have r₂ := eq28
       grind)
    | exact resolve eq10319 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10319
  have eq10332 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10330
    | exact resolve eq10330 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10330
  have eq10333 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10332
  have eq10337 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10333
  have eq10349 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq10337
    | exact resolve eq10337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10337
  have eq10477 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10349 eq10287
    | exact resolve eq10287 eq10349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10287 eq10349
  have eq10481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10477
  have eq10485 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10481
       have r₂ := eq28
       grind)
    | exact resolve eq10481 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10481
  have eq10601 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10485 eq72
    | (have r₁ := eq72
       have r₂ := eq10485
       grind)
    | exact resolve eq72 eq10485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq10602 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10485 eq28
    | exact resolve eq28 eq10485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10485
  have eq10603 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq10601
  have eq10725 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10603 eq109
    | exact resolve eq109 eq10603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10743 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq10725
  have eq10757 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10743
       have r₂ := eq10602
       grind)
    | exact resolve eq10743 eq10602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10743
  have eq10764 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq10757
  have eq10776 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq10764
    | exact resolve eq10764 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10764
  have eq10865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10776 eq109
    | exact resolve eq109 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq10776
  have eq10879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq10865
  have eq10883 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10879
       have r₂ := eq28
       grind)
    | exact resolve eq10879 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10879
  have eq10887 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq10883
  have eq10899 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10887
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10887
    | exact resolve eq10887 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10887
  have eq10906 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq10899
       grind)
    | exact superpose eq10899 eq68
    | exact resolve eq68 eq10899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10899
  have eq10924 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq10906
    | exact resolve eq10906 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10906
  have eq10946 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10924 eq10603
    | exact resolve eq10603 eq10924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10603
  have eq10952 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq10946
  have eq10960 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10952
       have r₂ := eq10602
       grind)
    | exact resolve eq10952 eq10602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10602 eq10952
  have eq10978 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq10960
  have eq10990 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq10978
    | exact resolve eq10978 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10978
  have eq11012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10990 eq10924
    | exact resolve eq10924 eq10990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10924 eq10990
  have eq11016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11012
  have eq11024 : y = (M.op x y) := by
    first
    | (have r₁ := eq11016
       have r₂ := eq28
       grind)
    | exact resolve eq11016 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11016
  have eq11026 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq11024 eq21
    | exact resolve eq21 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq11031 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq11024 eq71
    | (have r₁ := eq71
       have r₂ := eq11024
       grind)
    | exact resolve eq71 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq11080 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq11031
  have eq11131 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11026
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11026
    | exact resolve eq11026 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11026
  have eq11133 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq11131 eq27
    | exact resolve eq27 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq11278 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11080
       grind)
    | exact superpose eq11080 eq68
    | exact resolve eq68 eq11080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11288 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq626 x y
       have i₂ := eq11080
       grind)
    | exact superpose eq11080 eq626
    | (have j0 := eq626 x y
       grind)
    | exact resolve eq626 eq11080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11080
  have eq11291 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq11288
  have eq11298 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11291
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11291
    | exact resolve eq11291 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11291
  have eq11306 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11131 eq11278
    | exact resolve eq11278 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11278
  have eq11308 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11131 eq11298
    | exact resolve eq11298 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11298
  have eq11316 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11306
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11306
    | exact resolve eq11306 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11306
  have eq11317 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11308
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11308
    | exact resolve eq11308 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11308
  have eq11324 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11131 eq11316
    | exact resolve eq11316 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11316
  have eq11325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11133 eq11317
    | exact resolve eq11317 eq11133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11317
  have eq11327 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11325
       have r₂ := eq28
       grind)
    | exact resolve eq11325 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11325
  have eq11329 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11327
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11327
    | exact resolve eq11327 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11327
  have eq11331 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11329
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11329
    | exact resolve eq11329 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11329
  have eq11333 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11131 eq11331
    | exact resolve eq11331 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11331
  have eq11397 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq11333
  have eq11413 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11133 eq11397
    | exact resolve eq11397 eq11133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11397
  have eq11431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11413 eq11324
    | exact resolve eq11324 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11324 eq11413
  have eq11435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq11431
  have eq11437 : y = (M.op x x) := by
    first
    | (have r₁ := eq11435
       have r₂ := eq28
       grind)
    | exact resolve eq11435 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11435
  have eq11456 : (M.op x y) = (k y x) := by grind
  clear eq11437
  have eq11468 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq11456
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11456
    | exact resolve eq11456 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq11456
  have eq11470 : y = (k y x) := by
    first
    | exact superpose eq11024 eq11468
    | exact resolve eq11468 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11024 eq11468
  have eq11483 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11470
       grind)
    | exact superpose eq11470 eq68
    | exact resolve eq68 eq11470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq11493 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq626 x y
       have i₂ := eq11470
       grind)
    | exact superpose eq11470 eq626
    | (have j0 := eq626 x y
       grind)
    | exact resolve eq626 eq11470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq11470
  have eq11496 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq11493
  have eq11502 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11496
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11496
    | exact resolve eq11496 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11496
  have eq11510 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq11131 eq11483
    | exact resolve eq11483 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11483
  have eq11511 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11131 eq11502
    | exact resolve eq11502 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11502
  have eq11519 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq11510
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11510
    | exact resolve eq11510 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11510
  have eq11520 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11511
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11511
    | exact resolve eq11511 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11511
  have eq11527 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq11131 eq11519
    | exact resolve eq11519 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11519
  have eq11528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11133 eq11520
    | exact resolve eq11520 eq11133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11520
  have eq11530 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq11528
       have r₂ := eq28
       grind)
    | exact resolve eq11528 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11528
  have eq11532 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11530
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11530
    | exact resolve eq11530 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11530
  have eq11534 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11532
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11532
    | exact resolve eq11532 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11532
  have eq11536 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11131 eq11534
    | exact resolve eq11534 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11131 eq11534
  have eq11599 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq11536
  have eq11611 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq11133 eq11599
    | exact resolve eq11599 eq11133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11133 eq11599
  have eq11612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11527 eq11611
    | exact resolve eq11611 eq11527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11527 eq11611
  have eq11613 : False := by grind
  exact eq11613

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_x_pyx_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
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
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq14 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 x
       have i₂ := eq14 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq68 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq71 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 (M.op X2 (M.op X0 X0))) = (k (M.op X1 (M.op X2 (M.op X0 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) = (k (M.op X1 (M.op X2 (M.op X0 X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq72 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq78 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq68
       grind)
    | exact superpose eq68 eq16
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq89
    | (have j0 := eq89 (σ X0) (σ X1)
       grind)
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq89 y x
       grind)
    | exact superpose eq89 eq67
    | (have j1 := eq89 y x
       grind)
    | exact resolve eq67 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq89 sF3 sF2
       grind)
    | exact superpose eq89 eq78
    | (have j1 := eq89 (σ y) (σ x)
       grind)
    | exact resolve eq78 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq111 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq108
    | exact resolve eq108 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq113 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq111
    | exact resolve eq111 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115 eq89
    | (have j0 := eq89 (σ y) (σ x)
       grind)
    | exact resolve eq89 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq118
    | exact resolve eq118 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq119
       have r₂ := eq27
       grind)
    | exact resolve eq119 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq124 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq217 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq51 X0
       grind)
    | exact resolve eq12 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq304 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq407 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq67
    | exact resolve eq67 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq410 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq407
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq419 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq304
    | exact resolve eq304 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq458 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124 eq71
    | (have r₁ := eq71
       have r₂ := eq124
       grind)
    | exact resolve eq71 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq459 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq458
  have eq464 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq459 eq115
    | exact resolve eq115 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq467 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq464
  have eq475 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq467 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq467
       grind)
    | exact resolve eq13 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq477 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq475 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq484 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq50 X1 X0 X3
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq50 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y X0 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ y) X0 (σ x)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq477 eq115
    | exact resolve eq115 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq507
  have eq515 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq510
    | exact resolve eq510 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq517 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq515
       have r₂ := eq27
       grind)
    | exact resolve eq515 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq519 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq517 eq26
    | exact resolve eq26 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq517 eq29
    | exact resolve eq29 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq540 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq520
    | exact resolve eq520 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq520
  have eq583 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq648 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 (M.op (τ X2) (τ X2))))) = (k (σ (M.op X0 (M.op X1 (M.op (τ X2) (τ X2))))) X2) ∨ (τ X2) = (M.op (τ X2) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X2 (M.op X0 (M.op X1 (M.op (τ X2) (τ X2))))
       have i₂ := eq73 (τ X2) X0 X1
       grind)
    | exact superpose eq73 eq38
    | (have j1 := eq73 (τ X2) X1 X2
       grind)
    | exact resolve eq38 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq4727 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq218 X0
       grind)
    | exact superpose eq218 eq14
    | (have j1 := eq218 X0
       grind)
    | exact resolve eq14 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4734 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq218 X0
       grind)
    | exact superpose eq218 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       have j1 := eq218 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq218 X0
       grind)
    | exact resolve eq13 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq4737 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4734 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4734
  have eq5319 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq484 x X2 X0 X1
       grind)
    | exact superpose eq484 eq14
    | exact resolve eq14 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq6595 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X2 (M.op X0 X0)))) = (k (σ (M.op X1 (M.op X2 (M.op X0 X0)))) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq648 X0 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq648
    | exact resolve eq648 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq6700 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X2 (M.op X0 X0)))) = (σ (k (M.op X1 (M.op X2 (M.op X0 X0))) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6595 X0 X1 X2
       have i₂ := eq10 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       grind)
    | exact superpose eq10 eq6595
    | (have j0 := eq6595 X0 X1 X2
       grind)
    | exact resolve eq6595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6595
  have eq7551 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq583 (τ X1) (τ X0)
       have i₂ := eq419 X1 X0
       grind)
    | exact superpose eq419 eq583
    | (have j0 := eq583 (τ X1) (τ X0)
       grind)
    | exact resolve eq583 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq583
  have eq7553 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7551 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq7551
    | (have j0 := eq7551 X0 X1
       grind)
    | exact resolve eq7551 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7551
  have eq7597 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7553 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7553
    | (have j0 := eq7553 X0 X1
       grind)
    | exact resolve eq7553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7553
  have eq7611 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7597 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7597
    | (have j0 := eq7597 X0 X1
       grind)
    | exact resolve eq7597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7597
  have eq7619 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7611 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7611
    | (have j0 := eq7611 X0 X1
       grind)
    | exact resolve eq7611 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7611
  have eq25568 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq5319 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5319
    | (have j0 := eq5319 X0 x y
       grind)
    | exact resolve eq5319 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25576 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq519 eq5319
    | exact resolve eq5319 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq25584 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5319 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq5319 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq5319 eq5319
    | exact resolve eq5319 eq5319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25607 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq124 eq25576
    | exact resolve eq25576 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25613 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25576 eq73
    | (have j0 := eq73 (M.op (σ x) (σ y)) x x
       grind)
    | exact resolve eq73 eq25576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq25614 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25576 eq14
    | exact resolve eq14 eq25576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25628 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq25607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25607
  have eq25629 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124 eq25614
    | exact resolve eq25614 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq25635 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq25629
  have eq25663 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25628 eq14
    | exact resolve eq14 eq25628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25628
  have eq25675 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25613 eq25576
    | exact resolve eq25576 eq25613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25576 eq25613
  have eq25688 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq25675 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25675
  have eq43674 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 x
       have i₂ := eq4727 X0 x
       grind)
    | exact superpose eq4727 eq14
    | (have j1 := eq4727 X0 x
       grind)
    | exact resolve eq14 eq4727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4727
  have eq46959 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25614 eq25663
    | exact resolve eq25663 eq25614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25663
  have eq46972 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq46959
  have eq110837 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4737 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4737
  have eq110838 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq110837 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq110837
    | (have j0 := eq110837 X0
       grind)
    | exact resolve eq110837 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq110837
  have eq422615 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46972 eq25688
    | exact resolve eq25688 eq46972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25688 eq46972
  have eq422655 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq422615
  have eq442864 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq422655 eq14
    | exact resolve eq14 eq422655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422655
  have eq474023 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25635 eq442864
    | exact resolve eq442864 eq25635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25635 eq442864
  have eq474072 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq474023
  have eq474098 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq474072 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq474072
       grind)
    | exact resolve eq13 eq474072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474072
  have eq474126 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq474098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474098
  have eq512448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq474126 eq115
    | exact resolve eq115 eq474126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq474126
  have eq513227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq512448
  have eq513694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq513227
    | exact resolve eq513227 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513227
  have eq513730 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq513694
       have r₂ := eq27
       grind)
    | exact resolve eq513694 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513694
  have eq1147387 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq540 eq25568
    | exact resolve eq25568 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq1147570 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y y x
       have i₂ := eq1147387 x
       grind)
    | exact superpose eq1147387 eq14
    | exact resolve eq14 eq1147387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147387
  have eq1147714 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1147570
       grind)
    | exact superpose eq1147570 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1147570
       grind)
    | exact resolve eq13 eq1147570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1147785 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1147714 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147714
  have eq1149337 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq1147785 y
       grind)
    | exact superpose eq1147785 eq68
    | exact resolve eq68 eq1147785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1147785
  have eq1152812 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1149337
       have i₂ := eq1147570
       grind)
    | exact superpose eq1147570 eq1149337
    | exact resolve eq1149337 eq1147570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147570 eq1149337
  have eq1153210 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1152812
  have eq1153214 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1153210
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1153210
    | exact resolve eq1153210 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153210
  have eq1153431 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1153214 eq89
    | (have j0 := eq89 (σ y) (σ y)
       grind)
    | exact resolve eq89 eq1153214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1153214
  have eq1153447 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1153431
  have eq1153638 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1153447 eq486
    | exact resolve eq486 eq1153447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq1153447
  have eq1252127 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq110838 X0
       have j1 := eq43674 X0
       grind)
    | (have r₁ := eq110838 X0
       have r₂ := eq43674 X0
       grind)
    | exact resolve eq110838 eq43674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43674 eq110838
  have eq1431557 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1153638
    | (have j0 := eq1153638 (σ x)
       grind)
    | exact resolve eq1153638 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153638
  have eq1431623 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1431557 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (σ x) (σ y))
       have r₂ := eq1431557
       grind)
    | exact resolve eq13 eq1431557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431557
  have eq1431696 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1431623 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431623
  have eq1435081 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1431696 eq513730
    | exact resolve eq513730 eq1431696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513730 eq1431696
  have eq1435992 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1435081
  have eq1436072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1435992 eq25614
    | exact resolve eq25614 eq1435992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25614 eq1435992
  have eq1436112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1436072
  have eq1436119 : x = (M.op x y) := by
    first
    | (have r₁ := eq1436112
       have r₂ := eq27
       grind)
    | exact resolve eq1436112 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436112
  have eq1436580 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1436119 eq20
    | exact resolve eq20 eq1436119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1436939 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x x))) := by
    intro X0
    first
    | exact superpose eq1436119 eq25568
    | exact resolve eq25568 eq1436119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25568
  have eq1437211 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1436580
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1436580
    | exact resolve eq1436580 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1436580
  have eq1437214 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1437211 eq26
    | exact resolve eq26 eq1437211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1437260 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1437211 eq410
    | exact resolve eq410 eq1437211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq1437974 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1437260
       have r₂ := eq27
       grind)
    | exact resolve eq1437260 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437260
  have eq1438070 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1437214 eq25584
    | (have j0 := eq25584 (σ y) (σ x)
       grind)
    | exact resolve eq25584 eq1437214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25584 eq1437214
  have eq1438813 : (σ y) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6700 x y x
       have i₂ := eq1436939 x
       grind)
    | exact superpose eq1436939 eq6700
    | (have j0 := eq6700 x x x
       grind)
    | exact resolve eq6700 eq1436939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6700 eq1436939
  have eq1438927 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1438813
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq1438813
    | exact resolve eq1438813 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438813
  have eq1438937 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1437211 eq1438927
    | exact resolve eq1438927 eq1437211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438927
  have eq1438943 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1437974 eq1438937
    | exact resolve eq1438937 eq1437974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438937
  have eq1438949 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1438943
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1438943
    | exact resolve eq1438943 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1438943
  have eq1439726 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1438949
       grind)
    | exact superpose eq1438949 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1438949
       grind)
    | exact resolve eq13 eq1438949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438949
  have eq1439799 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1439726 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439726
  have eq1445767 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq1439799 y
       grind)
    | exact superpose eq1439799 eq67
    | exact resolve eq67 eq1439799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439799
  have eq1447264 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1437211 eq1445767
    | exact resolve eq1445767 eq1437211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445767
  have eq1447863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1437974 eq1447264
    | exact resolve eq1447264 eq1437974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447264
  have eq1448250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1447863
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1447863
    | exact resolve eq1447863 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447863
  have eq1448498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1448250
    | exact resolve eq1448250 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448250
  have eq1448613 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1448498
       have r₂ := eq27
       grind)
    | exact resolve eq1448498 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448498
  have eq1448670 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1448613 eq27
    | exact resolve eq27 eq1448613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1448726 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1448613 eq1438070
    | exact resolve eq1438070 eq1448613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438070
  have eq1448834 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1448726 eq1252127
    | exact resolve eq1252127 eq1448726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252127 eq1448726
  have eq1448902 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq1448834 eq83
    | exact resolve eq83 eq1448834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1448834
  have eq1449185 : y = (k y y) := by
    first
    | exact superpose eq29 eq1448902
    | exact resolve eq1448902 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1448902
  have eq1449385 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7619 y y
       have i₂ := eq1449185
       grind)
    | exact superpose eq1449185 eq7619
    | (have j0 := eq7619 y y
       grind)
    | (have r₁ := eq7619 y y
       have r₂ := eq1449185
       grind)
    | exact resolve eq7619 eq1449185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7619 eq1449185
  have eq1449387 : y = (M.op y y) := by grind
  clear eq1449385
  have eq1449793 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq5319 X0 y y
       have i₂ := eq1449387
       grind)
    | exact superpose eq1449387 eq5319
    | exact resolve eq5319 eq1449387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1449806 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1449793 X0
       have i₂ := eq1449387
       grind)
    | exact superpose eq1449387 eq1449793
    | exact resolve eq1449793 eq1449387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449793
  have eq1455613 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq485 y
       have i₂ := eq1449806 y
       grind)
    | exact superpose eq1449806 eq485
    | (have j1 := eq1449806 x
       grind)
    | exact resolve eq485 eq1449806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449806
  have eq1455658 : y = (M.op y x) := by
    first
    | exact superpose eq1436119 eq1455613
    | exact resolve eq1455613 eq1436119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455613
  have eq1455713 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq5319 X0 y x
       have i₂ := eq1455658
       grind)
    | exact superpose eq1455658 eq5319
    | exact resolve eq5319 eq1455658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319 eq1455658
  have eq1455734 : ∀ X0 : G, x = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1455713 X0
       have i₂ := eq1449387
       grind)
    | exact superpose eq1449387 eq1455713
    | exact resolve eq1455713 eq1449387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449387 eq1455713
  have eq1455826 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq485 x
       have i₂ := eq1455734 y
       grind)
    | exact superpose eq1455734 eq485
    | (have j1 := eq1455734 x
       grind)
    | exact resolve eq485 eq1455734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq1455734
  have eq1455860 : x = (M.op x x) := by
    first
    | exact superpose eq1436119 eq1455826
    | exact resolve eq1455826 eq1436119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436119 eq1455826
  have eq1455893 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1455860
       grind)
    | exact superpose eq1455860 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1455860
       grind)
    | exact resolve eq13 eq1455860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455860
  have eq1455966 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1455893 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455893
  have eq1458411 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq1455966 y
       grind)
    | exact superpose eq1455966 eq67
    | exact resolve eq67 eq1455966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1455966
  have eq1459930 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1437211 eq1458411
    | exact resolve eq1458411 eq1437211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437211 eq1458411
  have eq1460571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1437974 eq1459930
    | exact resolve eq1459930 eq1437974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437974 eq1459930
  have eq1461069 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1448613 eq1460571
    | exact resolve eq1460571 eq1448613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448613 eq1460571
  have eq1461504 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1461069
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1461069
    | exact resolve eq1461069 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1461069
  have eq1461828 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq1461504
    | exact resolve eq1461504 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1461504
  have eq1462095 : False := by grind
  exact eq1462095

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxx_pxx_pyx_Equation450 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  clear eq23
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) ≠ X0 ∨ (k (M.op X1 (M.op X2 (M.op X1 X0))) X0) = (M.op (M.op X1 (M.op X2 (M.op X1 X0))) (M.op X1 (M.op X2 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 (M.op X1 X0))) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op X2 (M.op X1 X0))) X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq118 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq123 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
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
  clear eq19
  have eq2310 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq16
    | (have j1 := eq118 x y
       grind)
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2319 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq7039 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq69 x x x
       have i₂ := eq73 x x
       grind)
    | exact superpose eq73 eq69
    | (have j1 := eq73 X0 x
       grind)
    | (have r₁ := eq69 x x x
       have r₂ := eq73 x x
       grind)
    | exact resolve eq69 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq73
  have eq7044 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7039
  have eq7045 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7044 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7044
  have eq7135 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7045 (σ X0)
       grind)
    | exact superpose eq7045 eq15
    | exact resolve eq15 eq7045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7154 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7135 X0
       have i₂ := eq7045 X0
       grind)
    | exact superpose eq7045 eq7135
    | exact resolve eq7135 eq7045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7045 eq7135
  have eq7312 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq7154 X0
       grind)
    | exact superpose eq7154 eq64
    | exact resolve eq64 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11176 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq123 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq123
    | exact resolve eq123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq11314 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11176 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq11176
    | (have j0 := eq11176 X0 X1
       grind)
    | exact resolve eq11176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11176
  have eq19042 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2319 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq2319
    | (have j0 := eq2319 (τ X0) (τ X1)
       grind)
    | exact resolve eq2319 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq19066 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19042 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq19042
    | (have j0 := eq19042 X0 X1
       grind)
    | exact resolve eq19042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19042
  have eq19076 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19066 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19066
    | (have j0 := eq19066 X0 X1
       grind)
    | exact resolve eq19066 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19066
  have eq19084 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19076 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19076
    | (have j0 := eq19076 X0 X1
       grind)
    | exact resolve eq19076 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19076
  have eq19086 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19084 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19084
    | (have j0 := eq19084 X0 X1
       grind)
    | exact resolve eq19084 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19084
  have eq19087 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19086 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19086
    | (have j0 := eq19086 X0 X1
       grind)
    | exact resolve eq19086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19086
  have eq19088 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19087 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19087
    | (have j0 := eq19087 X0 X1
       grind)
    | exact resolve eq19087 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19087
  have eq54024 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2310
       have i₂ := eq11314 x y
       grind)
    | exact superpose eq11314 eq2310
    | (have j1 := eq11314 (σ x) (σ y)
       grind)
    | (have r₁ := eq2310
       have r₂ := eq11314 x y
       grind)
    | (have r₁ := eq2310
       have r₂ := eq11314 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2310
       have r₂ := eq11314 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2310 eq11314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310 eq11314
  have eq54025 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq54024
  have eq100424 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54025
       grind)
    | exact superpose eq54025 eq16
    | exact resolve eq16 eq54025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54025
  have eq100425 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq100424
       have r₂ := eq7154 x
       grind)
    | exact resolve eq100424 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100424
  have eq100427 : y ≠ y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq100425
       grind)
    | exact superpose eq100425 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq100425
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq100425
       grind)
    | exact resolve eq12 eq100425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100430 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq64 y x
       have i₂ := eq100425
       grind)
    | exact superpose eq100425 eq64
    | exact resolve eq64 eq100425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100425
  have eq100445 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq100427
  have eq100453 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq64 (σ y) (σ x)
       have i₂ := eq100430
       grind)
    | exact superpose eq100430 eq64
    | exact resolve eq64 eq100430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq100430
  have eq100472 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq100453
       have i₂ := eq7154 y
       grind)
    | exact superpose eq7154 eq100453
    | exact resolve eq100453 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100453
  have eq100500 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq100472
       grind)
    | exact superpose eq100472 eq10
    | exact resolve eq10 eq100472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100472
  have eq100612 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq100500
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq100500
    | exact resolve eq100500 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100500
  have eq100651 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100612
       grind)
    | exact superpose eq100612 eq16
    | exact resolve eq16 eq100612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100612
  have eq100652 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq100651
       have r₂ := eq7154 x
       grind)
    | exact resolve eq100651 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100651
  have eq100666 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq100652
       grind)
    | exact superpose eq100652 eq10
    | exact resolve eq10 eq100652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100652
  have eq100778 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq100666
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq100666
    | exact resolve eq100666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100666
  have eq100779 : y = (M.op y y) := by grind
  clear eq100778
  have eq118723 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2319 x y
       have i₂ := eq100445
       grind)
    | exact superpose eq100445 eq2319
    | (have j0 := eq2319 x y
       grind)
    | exact resolve eq2319 eq100445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319 eq100445
  have eq118732 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq118723
  have eq118736 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq118732
       have i₂ := eq100779
       grind)
    | exact superpose eq100779 eq118732
    | exact resolve eq118732 eq100779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118732
  have eq118737 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq118736
  have eq118740 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118737
       grind)
    | exact superpose eq118737 eq16
    | exact resolve eq16 eq118737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118744 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq118737
       grind)
    | exact superpose eq118737 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq118737
       grind)
    | exact resolve eq12 eq118737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118737
  have eq118763 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq118744
  have eq118769 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq118763
       have i₂ := eq7154 y
       grind)
    | exact superpose eq7154 eq118763
    | exact resolve eq118763 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118763
  have eq118775 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq118769
       have i₂ := eq100779
       grind)
    | exact superpose eq100779 eq118769
    | exact resolve eq118769 eq100779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118769
  have eq118778 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq118775
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq118775
    | exact resolve eq118775 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118775
  have eq118823 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq118778
       grind)
    | exact superpose eq118778 eq10
    | exact resolve eq10 eq118778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118778
  have eq118944 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq118823
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq118823
    | exact resolve eq118823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118823
  have eq119004 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118944
       grind)
    | exact superpose eq118944 eq16
    | exact resolve eq16 eq118944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118944
  have eq119065 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq119004
       have r₂ := eq7154 x
       grind)
    | exact resolve eq119004 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119004
  have eq119076 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq119065
       grind)
    | exact superpose eq119065 eq10
    | exact resolve eq10 eq119065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119065
  have eq119188 : y = (k y x) := by
    first
    | (have i₁ := eq119076
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq119076
    | exact resolve eq119076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119076
  have eq119229 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19088 y x
       have i₂ := eq119188
       grind)
    | exact superpose eq119188 eq19088
    | (have j0 := eq19088 x y
       grind)
    | (have r₁ := eq19088 y x
       have r₂ := eq119188
       grind)
    | exact resolve eq19088 eq119188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19088 eq119188
  have eq119235 : x = y ∨ y = (M.op x y) := by grind
  clear eq119229
  have eq119241 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq119235
       grind)
    | exact superpose eq119235 eq16
    | exact resolve eq16 eq119235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119235
  have eq119306 : y = (M.op x y) := by
    first
    | (have r₁ := eq119241
       have r₂ := eq7154 x
       grind)
    | exact resolve eq119241 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119241
  have eq119311 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq118740
       have i₂ := eq119306
       grind)
    | exact superpose eq119306 eq118740
    | exact resolve eq118740 eq119306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118740
  have eq119365 : (σ x) = (σ y) := by grind
  clear eq119311
  have eq119380 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq119365
       grind)
    | exact superpose eq119365 eq16
    | exact resolve eq16 eq119365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119446 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ x)) := by
    first
    | (have i₁ := eq7312 y
       have i₂ := eq119365
       grind)
    | exact superpose eq119365 eq7312
    | exact resolve eq7312 eq119365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7312
  have eq119465 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq119446
       have i₂ := eq100779
       grind)
    | exact superpose eq100779 eq119446
    | exact resolve eq119446 eq100779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100779 eq119446
  have eq119507 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq119380
       have i₂ := eq7154 x
       grind)
    | exact superpose eq7154 eq119380
    | exact resolve eq119380 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119380
  have eq119515 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq119465
       have i₂ := eq119365
       grind)
    | exact superpose eq119365 eq119465
    | exact resolve eq119465 eq119365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119465
  have eq119538 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq119507
       have i₂ := eq119306
       grind)
    | exact superpose eq119306 eq119507
    | exact resolve eq119507 eq119306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119306 eq119507
  have eq119543 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq119515
       have i₂ := eq7154 x
       grind)
    | exact superpose eq7154 eq119515
    | exact resolve eq119515 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7154 eq119515
  have eq119565 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq119538
       have i₂ := eq119365
       grind)
    | exact superpose eq119365 eq119538
    | exact resolve eq119538 eq119365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119365 eq119538
  have eq119585 : False := by grind
  exact eq119585

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
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
  clear eq37
  have eq86 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq164 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq86 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq86
    | exact resolve eq86 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq177 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq202 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq191
    | exact resolve eq191 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq209 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq175
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq690 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op x x) X4 X5
       have i₂ := eq16 (M.op x x) x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | (have i₁ := eq16 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq694 x x X2 X3 X5
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq694
    | exact resolve eq694 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq704 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq703 x x X5
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq703
    | exact resolve eq703 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq705 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq695 X0 (M.op x x)
       have i₂ := eq695 (M.op x x) x
       grind)
    | exact superpose eq695 eq695
    | exact resolve eq695 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq695 x x
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq695 x x
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq695
    | exact resolve eq695 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq723 eq704
    | exact resolve eq704 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ X0 ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq704 eq13
    | (have j0 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq704 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq704 eq28
    | (have j0 := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq28 x (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq704 x
       grind)
    | exact resolve eq28 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq754 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq759 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq723 eq757
    | exact resolve eq757 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq761 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq723 eq752
    | (have j0 := eq752 X0
       grind)
    | (have r₁ := eq752 (M.op (M.op x y) y)
       have r₂ := eq723
       grind)
    | exact resolve eq752 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq766 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq723 eq761
    | (have j0 := eq761 X0
       grind)
    | (have r₁ := eq761 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq723
       grind)
    | exact resolve eq761 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq787 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq788 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq815 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq848 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1 x x
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq795
    | (have j0 := eq795 X0 X1 x x
       grind)
    | exact resolve eq795 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq795
  have eq865 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq723 eq848
    | (have j0 := eq848 X0 X1
       grind)
    | exact resolve eq848 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq993 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op x y) y) = X0 ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq705 eq11
    | (have j0 := eq11 (M.op (M.op x y) y) X0
       grind)
    | exact resolve eq11 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq993 X0
       have j1 := eq766 X0
       grind)
    | (have r₁ := eq993 X0
       have r₂ := eq766 (k (M.op (M.op x y) y) X0)
       grind)
    | (have r₁ := eq993 X0
       have r₂ := eq766 X0
       grind)
    | (have r₁ := eq993 (M.op (M.op x y) y)
       have r₂ := eq766 (M.op (M.op x y) y)
       grind)
    | exact resolve eq993 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq993
  have eq1002 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq999 X0
       have j1 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq999 x
       have r₂ := eq13 (M.op (M.op x y) y) x
       grind)
    | (have r₁ := eq999 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))
       grind)
    | exact resolve eq999 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1085 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (σ x)) := by
    first
    | exact superpose eq1002 eq40
    | exact resolve eq40 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1087 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1002 eq42
    | exact resolve eq42 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq2348 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq787
       grind)
    | exact superpose eq787 eq40
    | exact resolve eq40 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq2350 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2348
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2348
    | exact resolve eq2348 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq2352 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2350
    | exact resolve eq2350 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2625 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2352 eq788
    | exact resolve eq788 eq2352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2633 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2625
       have r₂ := eq27
       grind)
    | exact resolve eq2625 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2625
  have eq2638 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2633 eq220
    | exact resolve eq220 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq2656 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2633 eq709
    | exact resolve eq709 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2661 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq2656
    | exact resolve eq2656 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2656
  have eq2674 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq2638
    | exact resolve eq2638 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq2683 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2674
       have r₂ := eq176
       grind)
    | exact resolve eq2674 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq2674
  have eq2686 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq2683
       have r₂ := eq13 y x
       grind)
    | exact resolve eq2683 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2690 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2686
       grind)
    | exact superpose eq2686 eq40
    | exact resolve eq40 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2686
  have eq2691 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2690
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2690
    | exact resolve eq2690 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2690
  have eq2693 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2691
       have r₂ := eq177
       grind)
    | exact resolve eq2691 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2691
  have eq2697 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2693 eq2352
    | exact resolve eq2352 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352
  have eq2698 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2693 eq788
    | exact resolve eq788 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq2693
  have eq2713 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2697
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq2697
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq2697 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2718 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq695 X0 y
       have i₂ := eq2697
       grind)
    | exact superpose eq2697 eq695
    | exact resolve eq695 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2725 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq2697
       grind)
    | exact superpose eq2697 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2732 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq709 y y
       have i₂ := eq2697
       grind)
    | exact superpose eq2697 eq709
    | exact resolve eq709 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697
  have eq2734 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2725
  have eq2735 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq2713
  have eq2737 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2732
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2732
    | exact resolve eq2732 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732
  have eq2750 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2734 eq2735
    | exact resolve eq2735 eq2734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734 eq2735
  have eq2772 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2698 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698
  have eq2781 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2772
  have eq2860 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2737 eq743
    | exact resolve eq743 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2861 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2737 eq759
    | exact resolve eq759 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2883 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2737 eq1087
    | exact resolve eq1087 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq2933 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq2883
    | exact resolve eq2883 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2883
  have eq3709 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2933 eq815
    | (have j0 := eq815 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq815 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq2933
       grind)
    | exact resolve eq815 eq2933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2933
  have eq3710 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3709
  have eq3711 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3710
  have eq4253 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3711 eq709
    | exact resolve eq709 eq3711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4258 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2737 eq4253
    | exact resolve eq4253 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253
  have eq4327 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4258 eq3711
    | exact resolve eq3711 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3711 eq4258
  have eq4349 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq4327
  have eq4617 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq4349 eq29
    | exact resolve eq29 eq4349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4349
  have eq4661 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq4617
    | exact resolve eq4617 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4617
  have eq5549 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2718 eq2860
    | exact resolve eq2860 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718 eq2860
  have eq5594 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq5549 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5549
  have eq11506 : ∀ X0 : G, x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq2661 eq759
    | exact resolve eq759 eq2661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759 eq2661
  have eq11957 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X3 (M.op (σ x) (σ y))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq690 y y X2 X0 X1
       have i₂ := eq11506 X3
       grind)
    | exact superpose eq11506 eq690
    | (have j1 := eq11506 X3
       grind)
    | exact resolve eq690 eq11506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11962 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq709 y y
       have i₂ := eq11506 X0
       grind)
    | exact superpose eq11506 eq709
    | (have j1 := eq11506 X0
       grind)
    | exact resolve eq709 eq11506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11970 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11962 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11962
    | (have j0 := eq11962 X0
       grind)
    | exact resolve eq11962 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11962
  have eq11975 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X3 (M.op (σ x) (σ y))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11957 X0 X1 X2 X3
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11957
    | (have j0 := eq11957 X0 X1 X2 X3
       grind)
    | exact resolve eq11957 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11957
  have eq11988 : ∀ X2 X3 : G, (M.op (M.op x y) y) = (M.op X2 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X3 (M.op (σ x) (σ y))) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq11975 x x X2 X3
       have i₂ := eq709 x x
       grind)
    | (have i₁ := eq11975 x y X2 X3
       have i₂ := eq709 X2 X3
       grind)
    | exact superpose eq709 eq11975
    | (have j0 := eq11975 x y X2 X3
       grind)
    | exact resolve eq11975 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11975
  have eq11992 : ∀ X2 X3 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X3 (M.op (σ x) (σ y))) = X3 := by
    intro X2 X3
    first
    | exact superpose eq11970 eq11988
    | (have j0 := eq11988 X2 X3
       have j1 := eq11970 X3
       grind)
    | exact resolve eq11988 eq11970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11970 eq11988
  have eq13130 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2750
       grind)
    | exact superpose eq2750 eq41
    | exact resolve eq41 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2750
  have eq13148 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13130
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13130
    | exact resolve eq13130 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13130
  have eq13150 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13148
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13148
    | exact resolve eq13148 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13148
  have eq13152 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5594 eq13150
    | exact resolve eq13150 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5594 eq13150
  have eq13153 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13152
  have eq13159 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13153 eq116
    | exact resolve eq116 eq13153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq13167 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13153 eq865
    | (have j0 := eq865 (σ y) (σ y)
       grind)
    | exact resolve eq865 eq13153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq13171 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13167
  have eq13176 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq13171
    | exact resolve eq13171 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13171
  have eq13179 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq13159
    | exact resolve eq13159 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13159
  have eq13180 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2737 eq13176
    | exact resolve eq13176 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13176
  have eq13225 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq13180 eq695
    | exact resolve eq695 eq13180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13237 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13180 eq28
    | (have j0 := eq28 (σ y) (σ y)
       grind)
    | (have r₁ := eq28 (σ y) (σ y)
       have r₂ := eq13180
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq13180
       grind)
    | exact resolve eq28 eq13180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13180
  have eq13245 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13237
  have eq13258 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13153 eq13245
    | exact resolve eq13245 eq13153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13153 eq13245
  have eq13266 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2737 eq13225
    | exact resolve eq13225 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737 eq13225
  have eq13284 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq13258 eq13266
    | (have j0 := eq13266 (σ x)
       grind)
    | exact resolve eq13266 eq13258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13266
  have eq13311 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13258 eq26
    | exact resolve eq26 eq13258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13258
  have eq13440 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13284 eq13311
    | exact resolve eq13311 eq13284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13284 eq13311
  have eq13441 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq13440
  have eq13455 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13441 eq29
    | exact resolve eq29 eq13441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq13553 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq13455
    | exact resolve eq13455 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13455
  have eq13568 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13553 eq27
    | exact resolve eq27 eq13553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13553
  have eq13665 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13568
       have r₂ := eq4661
       grind)
    | exact resolve eq13568 eq4661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4661 eq13568
  have eq13667 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13665
       grind)
    | exact superpose eq13665 eq18
    | exact resolve eq18 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13754 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11506 X0
       have i₂ := eq13665
       grind)
    | exact superpose eq13665 eq11506
    | (have j0 := eq11506 X0
       grind)
    | exact resolve eq11506 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11506
  have eq13757 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13179
       have i₂ := eq13665
       grind)
    | exact superpose eq13665 eq13179
    | exact resolve eq13179 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13179
  have eq13758 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13757
  have eq13761 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq13754 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13754
  have eq13774 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2861 eq13758
    | exact resolve eq13758 eq2861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2861 eq13758
  have eq13775 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq13774
  have eq13776 : ∀ X0 : G, x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq11992 eq13761
    | (have j0 := eq13761 X0
       have j1 := eq11992 x X0
       grind)
    | exact resolve eq13761 eq11992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11992 eq13761
  have eq13777 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13776 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13776
  have eq14154 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13777 eq817
    | (have j0 := eq817 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq817 (M.op (σ x) (σ y))
       have r₂ := eq13777 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq817 eq13777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14158 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13777 eq35
    | exact resolve eq35 eq13777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq13777
  have eq14167 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14154
  have eq14179 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14158 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq14158
    | exact resolve eq14158 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14158
  have eq14192 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14167 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq14167
       grind)
    | exact resolve eq13 eq14167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14213 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14167 eq709
    | exact resolve eq709 eq14167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14224 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13665 eq14213
    | exact resolve eq14213 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14213
  have eq14239 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14167 eq14224
    | exact resolve eq14224 eq14167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14167 eq14224
  have eq14268 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14239 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op (σ x) (σ y))
       have r₂ := eq14239
       grind)
    | exact resolve eq13 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14282 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14239 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14285 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq14239 eq690
    | exact resolve eq690 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq14290 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14239 eq709
    | exact resolve eq709 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14292 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14282
  have eq14314 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13665 eq14290
    | exact resolve eq14290 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14290
  have eq14317 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq14285 x x X2
       have i₂ := eq709 x x
       grind)
    | (have i₁ := eq14285 x y X2
       have i₂ := eq709 X2 x
       grind)
    | exact superpose eq709 eq14285
    | (have j0 := eq14285 x y X2
       grind)
    | exact resolve eq14285 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14285
  have eq14327 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14239 eq14314
    | exact resolve eq14314 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14314
  have eq14330 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq13665 eq14317
    | exact resolve eq14317 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14317
  have eq14339 : ∀ X2 : G, (M.op (σ x) (σ y)) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq14239 eq14330
    | exact resolve eq14330 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14330
  have eq14343 : ∀ X2 : G, (M.op (σ x) (σ y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq14327 eq14339
    | exact resolve eq14339 eq14327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14327 eq14339
  have eq14636 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14343 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq14343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14343
  have eq14694 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14636 X0
       have j1 := eq14192 X0
       grind)
    | (have r₁ := eq14636 X0
       have r₂ := eq14192 (k (M.op (σ x) (σ y)) X0)
       grind)
    | (have r₁ := eq14636 X0
       have r₂ := eq14192 X0
       grind)
    | (have r₁ := eq14636 (M.op (σ x) (σ y))
       have r₂ := eq14192 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq14636 eq14192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14192 eq14636
  have eq14725 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14694 X0
       have j1 := eq13 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq14694 x
       have r₂ := eq13 (M.op (σ x) (σ y)) x
       grind)
    | (have r₁ := eq14694 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq14694 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14694
  have eq14765 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14725 eq164
    | exact resolve eq164 eq14725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq14725
  have eq15827 : (σ (M.op (σ x) (σ y))) ≠ (σ (M.op (σ x) (σ y))) ∨ (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14179 eq817
    | (have j0 := eq817 (σ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq817 (σ (M.op (σ x) (σ y)))
       have r₂ := eq14179 (σ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq817 eq14179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq14179
  have eq15855 : (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15827
  have eq18672 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15855 eq695
    | exact resolve eq695 eq15855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq18718 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13665 eq18672
    | exact resolve eq18672 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18672
  have eq18730 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14239 eq18718
    | exact resolve eq18718 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14239 eq18718
  have eq18806 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18730 eq15855
    | exact resolve eq15855 eq18730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15855 eq18730
  have eq18816 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18806
  have eq19402 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14292 eq42
    | exact resolve eq42 eq14292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14292
  have eq19423 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq19402
    | exact resolve eq19402 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19402
  have eq19426 : (k (σ y) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13441 eq19423
    | exact resolve eq19423 eq13441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13441 eq19423
  have eq19429 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18816 eq19426
    | exact resolve eq19426 eq18816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18816 eq19426
  have eq19656 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19429 eq2781
    | exact resolve eq2781 eq19429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781 eq19429
  have eq19677 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19656
  have eq20860 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19677 eq14765
    | exact resolve eq14765 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14765 eq19677
  have eq20891 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq20860
  have eq20940 : y = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq20891
    | exact resolve eq20891 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20891
  have eq20966 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13665 eq20940
    | exact resolve eq20940 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20940
  have eq20973 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq14268 (M.op x y)
       grind)
    | (have r₁ := eq20966
       have r₂ := eq14268 (σ x)
       grind)
    | (have r₁ := eq20966
       have r₂ := eq14268 (M.op x y)
       grind)
    | exact resolve eq20966 eq14268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14268 eq20966
  have eq21017 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20973 eq42
    | exact resolve eq42 eq20973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq21022 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20973 eq815
    | (have j0 := eq815 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq815 (M.op x y) (M.op x y)
       have r₂ := eq20973
       grind)
    | exact resolve eq815 eq20973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20973
  have eq21023 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21022
  have eq21024 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21023
  have eq21032 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq21017
    | exact resolve eq21017 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21017
  have eq21034 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13775 eq21032
    | exact resolve eq21032 eq13775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13775 eq21032
  have eq21671 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21034 eq815
    | (have j0 := eq815 (σ y) (σ y)
       grind)
    | (have r₁ := eq815 (σ y) (σ y)
       have r₂ := eq21034
       grind)
    | exact resolve eq815 eq21034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21034
  have eq21672 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21671
  have eq21673 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21672
  have eq23780 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21673 eq2633
    | exact resolve eq2633 eq21673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633 eq21673
  have eq23819 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq23780
  have eq23840 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13665 eq23819
    | exact resolve eq23819 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23819
  have eq23857 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21024 eq23840
    | exact resolve eq23840 eq21024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21024 eq23840
  have eq23858 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq23857
  have eq23879 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23858 eq704
    | exact resolve eq704 eq23858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq23880 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23858 eq723
    | exact resolve eq723 eq23858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq23901 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq23880
    | exact resolve eq23880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23880
  have eq23902 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq23879
    | (have j0 := eq23879 X0
       grind)
    | exact resolve eq23879 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23879
  have eq23906 : (σ x) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23858 eq23901
    | exact resolve eq23901 eq23858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23901
  have eq23907 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23858 eq23902
    | exact resolve eq23902 eq23858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23858 eq23902
  have eq23909 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13665 eq23906
    | exact resolve eq23906 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23906
  have eq23956 : x = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23907 eq202
    | exact resolve eq202 eq23907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq24088 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq23956
    | exact resolve eq23956 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23956
  have eq24393 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq815 x x
       have i₂ := eq24088
       grind)
    | exact superpose eq24088 eq815
    | (have j0 := eq815 x x
       grind)
    | (have r₁ := eq815 x x
       have r₂ := eq24088
       grind)
    | exact resolve eq815 eq24088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24088
  have eq24394 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq24393
  have eq24395 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq24394
  have eq24604 : (M.op x x) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq709 x x
       have i₂ := eq24395
       grind)
    | exact superpose eq24395 eq709
    | exact resolve eq709 eq24395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq24621 : x = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24395 eq24604
    | exact resolve eq24604 eq24395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24395 eq24604
  have eq24635 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13665 eq24621
    | exact resolve eq24621 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24621
  have eq24646 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23909 eq24635
    | exact resolve eq24635 eq23909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23909 eq24635
  have eq24663 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24646 eq32
    | exact resolve eq32 eq24646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24646
  have eq24815 : x = y ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq24663
    | exact resolve eq24663 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24663
  have eq24831 : x = (M.op x y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13665 eq24815
    | exact resolve eq24815 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24815
  have eq24832 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq24831
  have eq24873 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13667
       have i₂ := eq24832
       grind)
    | exact superpose eq24832 eq13667
    | exact resolve eq13667 eq24832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13667
  have eq24887 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq24832
  have eq24889 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24873
       have r₂ := eq24887
       grind)
    | exact resolve eq24873 eq24887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24873
  have eq25666 : (M.op x y) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24889 eq23907
    | exact resolve eq23907 eq24889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23907 eq24889
  have eq25680 : (M.op x y) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq25666
  have eq25690 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25680
       have r₂ := eq24887
       grind)
    | exact resolve eq25680 eq24887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24887 eq25680
  have eq25697 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25690 eq32
    | exact resolve eq32 eq25690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq25690
  have eq25849 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq25697
    | exact resolve eq25697 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq25697
  have eq25867 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13665 eq25849
    | exact resolve eq25849 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13665 eq25849
  have eq25868 : x = (M.op x y) := by grind
  clear eq25867
  have eq25885 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25868
       grind)
    | exact superpose eq25868 eq18
    | exact resolve eq18 eq25868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25886 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq25868
       grind)
    | exact superpose eq25868 eq22
    | exact resolve eq22 eq25868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25868
  have eq25907 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq25886 eq20
    | exact resolve eq20 eq25886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25886
  have eq26111 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq25885 eq705
    | exact resolve eq705 eq25885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq26117 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq25885 eq743
    | exact resolve eq743 eq25885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq26139 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq25885 eq1085
    | exact resolve eq1085 eq25885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq25885
  have eq26201 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq26139
    | exact resolve eq26139 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq26139
  have eq26225 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq25907 eq26201
    | exact resolve eq26201 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26201
  have eq26304 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26111 eq16
    | exact resolve eq16 eq26111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26111
  have eq26717 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26225 eq815
    | (have j0 := eq815 (σ x) (σ x)
       grind)
    | (have r₁ := eq815 (σ x) (σ x)
       have r₂ := eq26225
       grind)
    | exact resolve eq815 eq26225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq26225
  have eq26718 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq26717
  have eq26719 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq26718
  have eq26924 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26719 eq16
    | exact resolve eq16 eq26719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26943 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq26719 eq26924
    | exact resolve eq26924 eq26719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26719 eq26924
  have eq26955 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq26943 x x
       have i₂ := eq26304 x x
       grind)
    | exact superpose eq26304 eq26943
    | exact resolve eq26943 eq26304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26304 eq26943
  have eq26958 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq26955 eq26
    | exact resolve eq26 eq26955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq27045 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26117 eq26958
    | exact resolve eq26958 eq26117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26117 eq26958
  have eq27086 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq27045 eq27
    | exact resolve eq27 eq27045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq27045
  have eq27191 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq25907 eq27086
    | exact resolve eq27086 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25907 eq27086
  have eq27194 : False := by grind
  exact eq27194
