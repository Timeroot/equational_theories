import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2890`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation2890 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2890 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2890.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 (M.op x x)) x) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X3) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X3) X0 X1
       have i₂ := eq9 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 (M.op (M.op X0 (M.op X1 X2)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X0) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 (M.op (M.op X0 X1) X1)
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op X0 X0)
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X0 X1) X2) X2) X0 X1
       have i₂ := eq20 X2 (M.op X0 X1)
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq38 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq41 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op X0 (M.op X1 X2)) X2) X0) = X0 ∨ (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 (M.op X1 X2)) X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op X0 (M.op X1 X2)) X2) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 (M.op X1 X2)) X2) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq26 X0
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq48 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq51 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X2)) X2) X0) = X0 ∨ (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq46 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq137 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X1) X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op (M.op (τ X0) (M.op X1 X2)) X2)) X0) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (M.op X1 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (M.op (M.op (τ X0) (M.op X1 X2)) X2)
       have i₂ := eq51 (τ X0) X1 X2
       grind)
    | exact superpose eq51 eq19
    | (have j1 := eq51 (τ X0) X1 X2
       grind)
    | exact resolve eq19 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq170 : ∀ X0 X1 X2 : G, (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (M.op X1 X2)) X2) ∨ (k (σ (M.op (M.op (τ X0) (M.op X1 X2)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq164 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq164
    | (have j0 := eq164 X0 X1 X2
       grind)
    | exact resolve eq164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq178 : ∀ X0 X1 : G, (σ (k X1 (k (τ (M.op (σ X0) (σ X0))) X0))) = (k (σ X1) (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0 X1
    grind
  clear eq34
  have eq212 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) X2) = (M.op X0 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op X0 X0) X0 X1 X2
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq21
    | exact resolve eq21 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X3) X3) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) (M.op X2 X3)) X3
       have i₂ := eq21 X0 X1 X2 X3
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X0 X1 X2
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq41
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq41 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq309 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X1) X1) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op (M.op X0 X1) X1) X1 X0 X0
       have i₂ := eq137 X0 X1
       grind)
    | exact superpose eq137 eq21
    | exact resolve eq21 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq917 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq49
  have eq925 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq917 X0
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq917
    | (have j0 := eq917 X0
       grind)
    | exact resolve eq917 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq917
  have eq926 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq925 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq934 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq926 (σ x)
       have i₂ := eq76 x x
       grind)
    | exact superpose eq76 eq926
    | (have j1 := eq76 X0 X0
       grind)
    | exact resolve eq926 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq947 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq934 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq952 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq947 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq947
    | (have j0 := eq947 X0
       grind)
    | exact resolve eq947 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1110 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1143 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1110 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1110
    | (have j0 := eq1110 X0 X1
       grind)
    | exact resolve eq1110 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1448 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq242 (M.op X1 X1) X1 X2 x
       have i₂ := eq20 X1 X1
       grind)
    | exact superpose eq20 eq242
    | exact resolve eq242 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq1654 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq323 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq323
    | (have j0 := eq323 (σ X0) (σ X1)
       grind)
    | exact resolve eq323 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq1732 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X2) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1448 X0 (M.op (M.op X0 X0) (M.op X1 X2)) X2
       have i₂ := eq21 X0 X0 X1 X2
       grind)
    | exact superpose eq21 eq1448
    | exact resolve eq1448 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq2173 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X1) X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1732 X0 (M.op X0 X1) X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq1732
    | exact resolve eq1732 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2243 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq309
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq309
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq309 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq2244 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq2243
  have eq2303 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2173 (M.op (M.op X0 X0) (M.op X1 X0)) X0
       have i₂ := eq1732 X0 X1 X0
       grind)
    | exact superpose eq1732 eq2173
    | exact resolve eq2173 eq1732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2601 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op (τ X0) (M.op X1 X2)) X2)) X0) = (σ (M.op (M.op (M.op (τ X0) (M.op X1 X2)) X2) (τ X0))) ∨ (k (σ (M.op (M.op (τ X0) (M.op X1 X2)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0
       have i₂ := eq170 X0 X1 X2
       grind)
    | exact superpose eq170 eq38
    | (have j1 := eq170 X0 X1 X2
       grind)
    | exact resolve eq38 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq170
  have eq2711 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op (M.op (τ X0) (M.op X1 X2)) X2)) X0) ∨ (k (σ (M.op (M.op (τ X0) (M.op X1 X2)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2601 X0 X1 X2
       have i₂ := eq9 (τ X0) X1 X2
       grind)
    | exact superpose eq9 eq2601
    | (have j0 := eq2601 X0 X1 X2
       grind)
    | exact resolve eq2601 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601
  have eq2717 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op (τ X0) (M.op X1 X2)) X2)) X0) = X0 ∨ (k (σ (M.op (M.op (τ X0) (M.op X1 X2)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2711 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2711
    | (have j0 := eq2711 X0 X1 X2
       grind)
    | exact resolve eq2711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2718 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op (τ X0) (M.op X1 X2)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2717 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717
  have eq2784 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op (τ (σ X0)) (M.op X1 X2)) X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 (σ (M.op (M.op (τ (σ X0)) (M.op X1 X2)) X2)) X0
       have i₂ := eq2718 (σ X0) X1 X2
       grind)
    | exact superpose eq2718 eq36
    | exact resolve eq36 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718
  have eq2795 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (M.op (M.op (τ (σ X0)) (M.op X1 X2)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2784 X0 X1 X2
       have i₂ := eq10 (M.op (M.op (τ (σ X0)) (M.op X1 X2)) X2)
       grind)
    | exact superpose eq10 eq2784
    | exact resolve eq2784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq2816 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X2)) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2795 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2795
    | exact resolve eq2795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2795
  have eq2848 : ∀ X0 X1 : G, (k (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2816 X1 (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op x x)) x) x) x) X0
       have i₂ := eq1732 X0 x x
       grind)
    | exact superpose eq1732 eq2816
    | exact resolve eq2816 eq1732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq2860 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2816 X0 (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) X2
       have i₂ := eq212 X0 X1 X2
       grind)
    | exact superpose eq212 eq2816
    | exact resolve eq2816 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq2816
  have eq3076 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X0) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2848 X0 (M.op (M.op X0 X1) X1)
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq2848
    | exact resolve eq2848 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848
  have eq7113 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X2) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2860 X0 (M.op (M.op X0 X0) (M.op X1 X2)) X2
       have i₂ := eq21 X0 X0 X1 X2
       grind)
    | exact superpose eq21 eq2860
    | exact resolve eq2860 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq7114 : ∀ X0 X1 : G, (k (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X1) X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2860 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq29 X0 X0 X1
       grind)
    | exact superpose eq29 eq2860
    | exact resolve eq2860 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2860
  have eq7407 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (M.op (M.op (M.op (M.op (σ X0) (σ X0)) X1) X1) X1) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (M.op (M.op (M.op (M.op (M.op (σ X0) (σ X0)) X1) X1) X1) X1) X0
       have i₂ := eq7114 (σ X0) X1
       grind)
    | exact superpose eq7114 eq36
    | exact resolve eq36 eq7114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq7419 : ∀ X0 X1 : G, (k (τ (M.op (M.op (M.op (M.op (M.op (σ X0) (σ X0)) X1) X1) X1) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7407 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7407
    | exact resolve eq7407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7407
  have eq11123 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X2) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7113 X0 (M.op X0 (M.op X1 X2)) X2
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq7113
    | exact resolve eq7113 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq7113
  have eq20038 : ∀ X0 X1 : G, (k (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X1 X0))) (M.op (M.op X0 X0) (M.op X1 X0))) (M.op (M.op X0 X0) (M.op X1 X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7114 X0 (M.op (M.op X0 X0) (M.op X1 X0))
       have i₂ := eq2303 X0 X1
       grind)
    | exact superpose eq2303 eq7114
    | exact resolve eq7114 eq2303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7114
  have eq20042 : ∀ X0 X1 : G, (k (τ (M.op (M.op (M.op (M.op (M.op (σ X0) (σ X0)) (M.op X1 (σ X0))) (M.op (M.op (σ X0) (σ X0)) (M.op X1 (σ X0)))) (M.op (M.op (σ X0) (σ X0)) (M.op X1 (σ X0)))) (M.op (M.op (σ X0) (σ X0)) (M.op X1 (σ X0))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7419 X0 (M.op (M.op (σ X0) (σ X0)) (M.op X1 (σ X0)))
       have i₂ := eq2303 (σ X0) X1
       grind)
    | exact superpose eq2303 eq7419
    | exact resolve eq7419 eq2303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2303 eq7419
  have eq20159 : ∀ X0 X1 : G, (k (τ (M.op (M.op (σ X0) (σ X0)) (M.op X1 (σ X0)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20042 X0 X1
       have i₂ := eq20 (M.op (M.op (σ X0) (σ X0)) (M.op X1 (σ X0))) (M.op (M.op (σ X0) (σ X0)) (M.op X1 (σ X0)))
       grind)
    | exact superpose eq20 eq20042
    | exact resolve eq20042 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20042
  have eq20161 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20038 X0 X1
       have i₂ := eq20 (M.op (M.op X0 X0) (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X1 X0))
       grind)
    | exact superpose eq20 eq20038
    | exact resolve eq20038 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20038
  have eq32480 : y ≠ y ∨ y = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2244
       grind)
    | exact superpose eq2244 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2244
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2244
       grind)
    | exact resolve eq13 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq32578 : y ≠ y ∨ y = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32480
  have eq32579 : y = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32578
  have eq37227 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (k X0 (τ (σ X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq926 (σ X0)
       have i₂ := eq262 X0 (σ X0) X0
       grind)
    | exact superpose eq262 eq926
    | (have j1 := eq262 X0 (σ X0) x
       grind)
    | exact resolve eq926 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq926
  have eq37240 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (k X0 (τ (σ X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq37227 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37227
  have eq37250 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37240 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37240
    | (have j0 := eq37240 X0
       grind)
    | exact resolve eq37240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37240
  have eq41019 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq952 X0
       have i₂ := eq37250 X0
       grind)
    | exact superpose eq37250 eq952
    | (have j0 := eq952 X0
       have j1 := eq37250 X0
       grind)
    | exact resolve eq952 eq37250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq37250
  have eq41108 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq41019 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41019
  have eq43017 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq41108
  have eq43191 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43017 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq43017
    | (have j0 := eq43017 X0
       grind)
    | exact resolve eq43017 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43017
  have eq43192 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq43191 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43191
  have eq43235 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq43192 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43192
    | exact resolve eq43192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43306 : ∀ X0 : G, (k (τ (M.op (σ (k X0 X0)) (σ (k X0 X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20159 X0 (σ X0)
       have i₂ := eq43192 X0
       grind)
    | exact superpose eq43192 eq20159
    | exact resolve eq20159 eq43192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20159
  have eq43471 : ∀ X0 : G, (σ X0) = (k (M.op (σ (k X0 X0)) (σ (k X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20161 (σ X0) (σ X0)
       have i₂ := eq43192 X0
       grind)
    | exact superpose eq43192 eq20161
    | exact resolve eq20161 eq43192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20161
  have eq43489 : ∀ X0 : G, (σ X0) = (k (σ (k (k X0 X0) (k X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq43471 X0
       have i₂ := eq43192 (k X0 X0)
       grind)
    | exact superpose eq43192 eq43471
    | exact resolve eq43471 eq43192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43471
  have eq43513 : ∀ X0 : G, (k (τ (σ (k (k X0 X0) (k X0 X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43306 X0
       have i₂ := eq43192 (k X0 X0)
       grind)
    | exact superpose eq43192 eq43306
    | exact resolve eq43306 eq43192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43306
  have eq43550 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq43235 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq43235
    | exact resolve eq43235 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43235
  have eq43551 : ∀ X0 : G, (σ X0) = (σ (k (k (k X0 X0) (k X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq43489 X0
       have i₂ := eq15 (k (k X0 X0) (k X0 X0)) X0
       grind)
    | exact superpose eq15 eq43489
    | exact resolve eq43489 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43489
  have eq43556 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43513 X0
       have i₂ := eq10 (k (k X0 X0) (k X0 X0))
       grind)
    | exact superpose eq10 eq43513
    | exact resolve eq43513 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43513
  have eq43569 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq43550 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43550
    | exact resolve eq43550 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43550
  have eq56879 : ∀ X0 X1 : G, (k (σ X0) (M.op (M.op (σ X1) (σ X1)) (σ X1))) = (σ (k (k (k (k X0 X0) (k X0 X0)) X0) (k (τ (M.op (σ X1) (σ X1))) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 (k (k (k X0 X0) (k X0 X0)) X0)
       have i₂ := eq43551 X0
       grind)
    | exact superpose eq43551 eq178
    | exact resolve eq178 eq43551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq56937 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (k (k X0 X0) (k X0 X0)) X0) (k (k (k X0 X0) (k X0 X0)) X0))) := by
    intro X0
    first
    | (have i₁ := eq43192 (k (k (k X0 X0) (k X0 X0)) X0)
       have i₂ := eq43551 X0
       grind)
    | exact superpose eq43551 eq43192
    | exact resolve eq43192 eq43551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43551
  have eq56957 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op (k (k (k X0 X0) (k X0 X0)) X0) (k (k (k X0 X0) (k X0 X0)) X0))) := by
    intro X0
    first
    | (have i₁ := eq56937 X0
       have i₂ := eq43569 (k (k (k X0 X0) (k X0 X0)) X0)
       grind)
    | exact superpose eq43569 eq56937
    | exact resolve eq56937 eq43569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56937
  have eq57009 : ∀ X0 X1 : G, (k (σ X0) (M.op (σ (k X1 X1)) (σ X1))) = (σ (k (k (k (k X0 X0) (k X0 X0)) X0) (k (τ (σ (k X1 X1))) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq56879 X0 X0
       have i₂ := eq43192 X0
       grind)
    | exact superpose eq43192 eq56879
    | exact resolve eq56879 eq43192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56879
  have eq57064 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56957 X0
       have i₂ := eq43556 X0
       grind)
    | exact superpose eq43556 eq56957
    | exact resolve eq56957 eq43556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56957
  have eq57074 : ∀ X0 X1 : G, (k (σ X0) (M.op (σ (k X1 X1)) (σ X1))) = (σ (k (k (k (k X0 X0) (k X0 X0)) X0) (k (k X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq57009 X0 X1
       have i₂ := eq10 (k X1 X1)
       grind)
    | exact superpose eq10 eq57009
    | exact resolve eq57009 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57009
  have eq57101 : ∀ X0 X1 : G, (k (σ X0) (M.op (σ (M.op X1 X1)) (σ X1))) = (σ (k (k (k (k X0 X0) (k X0 X0)) X0) (k (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq57074 X0 X0
       have i₂ := eq43569 X0
       grind)
    | exact superpose eq43569 eq57074
    | exact resolve eq57074 eq43569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57074
  have eq57122 : ∀ X0 X1 : G, (k (σ X0) (M.op (σ (M.op X1 X1)) (σ X1))) = (σ (k (k (k (k X0 X0) (k X0 X0)) X0) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    grind
  clear eq57101
  have eq57139 : ∀ X0 X1 : G, (σ (k X0 (M.op (M.op X1 X1) X1))) = (k (σ X0) (M.op (σ (M.op X1 X1)) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq57122 X0 X1
       have i₂ := eq43556 X0
       grind)
    | exact superpose eq43556 eq57122
    | exact resolve eq57122 eq43556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43556 eq57122
  have eq57422 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3076 (σ X0) (σ X0)
       have i₂ := eq57064 X0
       grind)
    | exact superpose eq57064 eq3076
    | exact resolve eq3076 eq57064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57064
  have eq57467 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq57422 X0
       have i₂ := eq57139 (M.op X0 X0) X0
       grind)
    | exact superpose eq57139 eq57422
    | exact resolve eq57422 eq57139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57139 eq57422
  have eq57563 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57467 X0
       have i₂ := eq3076 X0 X0
       grind)
    | exact superpose eq3076 eq57467
    | exact resolve eq57467 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3076 eq57467
  have eq122765 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1654 (τ X0) (τ X1)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq1654
    | (have j0 := eq1654 (τ X0) (τ X1)
       grind)
    | exact resolve eq1654 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1654
  have eq123087 : ∀ X0 X1 : G, (σ X1) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq122765 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq122765
    | (have j0 := eq122765 X0 X1
       grind)
    | exact resolve eq122765 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122765
  have eq123314 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq123087 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq123087
    | (have j0 := eq123087 X0 X1
       grind)
    | exact resolve eq123087 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123087
  have eq123519 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq123314 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq123314
    | (have j0 := eq123314 X0 X1
       grind)
    | exact resolve eq123314 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123314
  have eq123701 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq123519 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq123519
    | (have j0 := eq123519 X0 X1
       grind)
    | exact resolve eq123519 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123519
  have eq123794 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123701 X0 X1
       have i₂ := eq43192 (σ (τ X1))
       grind)
    | exact superpose eq43192 eq123701
    | (have j0 := eq123701 X0 X1
       grind)
    | exact resolve eq123701 eq43192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123701
  have eq123871 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123794 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq123794
    | (have j0 := eq123794 X0 X1
       grind)
    | exact resolve eq123794 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123794
  have eq123930 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123871 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq123871
    | (have j0 := eq123871 X0 X1
       grind)
    | exact resolve eq123871 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq123871
  have eq123974 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123930 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq123930
    | (have j0 := eq123930 X0 X1
       grind)
    | exact resolve eq123930 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123930
  have eq124007 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123974 X0 X1
       have i₂ := eq43569 X1
       grind)
    | exact superpose eq43569 eq123974
    | (have j0 := eq123974 X0 X1
       grind)
    | exact resolve eq123974 eq43569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123974
  have eq124039 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124007 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq124007
    | (have j0 := eq124007 X0 X1
       grind)
    | exact resolve eq124007 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124007
  have eq530959 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X1) X1) = (k (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X0) X0) X0) X0) (M.op (M.op (M.op (M.op X0 X1) X1) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11123 (M.op (M.op (M.op (M.op X0 X1) X1) X1) X1) (M.op X0 X0) X0
       have i₂ := eq657 X0 X1
       grind)
    | exact superpose eq657 eq11123
    | exact resolve eq11123 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq11123
  have eq531218 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X1) X1) = (k X0 (M.op (M.op (M.op (M.op X0 X1) X1) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq530959 X0 X1
       have i₂ := eq2173 X0 X0
       grind)
    | exact superpose eq2173 eq530959
    | exact resolve eq530959 eq2173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173 eq530959
  have eq2577348 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq124039 x y
       have i₂ := eq32579
       grind)
    | exact superpose eq32579 eq124039
    | (have j0 := eq124039 x y
       grind)
    | exact resolve eq124039 eq32579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32579 eq124039
  have eq2577377 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2577348
  have eq2577378 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2577377
  have eq2577424 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2577378
       have i₂ := eq43192 y
       grind)
    | exact superpose eq43192 eq2577378
    | exact resolve eq2577378 eq43192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43192 eq2577378
  have eq2577432 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2577424
       have i₂ := eq43569 y
       grind)
    | exact superpose eq43569 eq2577424
    | exact resolve eq2577424 eq43569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43569 eq2577424
  have eq2577433 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2577432
  have eq2577451 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2577433
       grind)
    | exact superpose eq2577433 eq16
    | exact resolve eq16 eq2577433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2578012 : (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ y)) = (k (σ x) (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq531218 (σ x) (σ y)
       have i₂ := eq2577433
       grind)
    | exact superpose eq2577433 eq531218
    | exact resolve eq531218 eq2577433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531218 eq2577433
  have eq2578066 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2578012
       have i₂ := eq20 (σ y) (σ y)
       grind)
    | exact superpose eq20 eq2578012
    | exact resolve eq2578012 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2578012
  have eq2578177 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2578066
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2578066
    | exact resolve eq2578066 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578066
  have eq2584983 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1143 x y
       have i₂ := eq2578177
       grind)
    | exact superpose eq2578177 eq1143
    | (have j0 := eq1143 x y
       grind)
    | exact resolve eq1143 eq2578177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq2578177
  have eq2585897 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2584983
  have eq2586377 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2585897
       have r₂ := eq2577451
       grind)
    | exact resolve eq2585897 eq2577451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2585897
  have eq2590520 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2577451
       have i₂ := eq2586377
       grind)
    | exact superpose eq2586377 eq2577451
    | exact resolve eq2577451 eq2586377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577451 eq2586377
  have eq2591071 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2590520
  have eq2591072 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2591071
  have eq2594874 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2591072
       grind)
    | exact superpose eq2591072 eq10
    | exact resolve eq10 eq2591072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591072
  have eq2596236 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2594874
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2594874
    | exact resolve eq2594874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594874
  have eq2596237 : x = (M.op y y) := by grind
  clear eq2596236
  have eq2596934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57563 y
       have i₂ := eq2596237
       grind)
    | exact superpose eq2596237 eq57563
    | exact resolve eq57563 eq2596237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57563 eq2596237
  have eq2597946 : False := by grind
  exact eq2597946

/-- `Equation2919`: `x = ((y ◇ (x ◇ z)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation2919 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2919 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2919.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq158 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq160 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq908 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq160 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq160
    | exact resolve eq160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq945 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq908 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq908
    | (have j0 := eq908 X0 X1
       grind)
    | exact resolve eq908 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq2800 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq16
    | (have j1 := eq158 x y
       grind)
    | exact resolve eq16 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2811 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq4568 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2811 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq2811
    | (have j0 := eq2811 (τ X0) (τ X1)
       grind)
    | exact resolve eq2811 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq4609 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4568 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4568
    | (have j0 := eq4568 X0 X1
       grind)
    | exact resolve eq4568 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4568
  have eq4627 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4609 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4609
    | (have j0 := eq4609 X0 X1
       grind)
    | exact resolve eq4609 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4609
  have eq4644 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4627 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4627
    | (have j0 := eq4627 X0 X1
       grind)
    | exact resolve eq4627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627
  have eq4657 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4644 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4644
    | (have j0 := eq4644 X0 X1
       grind)
    | exact resolve eq4644 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644
  have eq4666 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4657 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4657
    | (have j0 := eq4657 X0 X1
       grind)
    | exact resolve eq4657 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq4671 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4666 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4666
    | (have j0 := eq4666 X0 X1
       grind)
    | exact resolve eq4666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666
  have eq13606 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2800
       have i₂ := eq945 x y
       grind)
    | exact superpose eq945 eq2800
    | (have j1 := eq945 (σ x) (σ y)
       grind)
    | (have r₁ := eq2800
       have r₂ := eq945 x y
       grind)
    | (have r₁ := eq2800
       have r₂ := eq945 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2800
       have r₂ := eq945 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2800 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq2800
  have eq13607 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13606
  have eq14277 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13607
       grind)
    | exact superpose eq13607 eq16
    | exact resolve eq16 eq13607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13607
  have eq14278 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14277
       have r₂ := eq22 x
       grind)
    | exact resolve eq14277 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14277
  have eq14280 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq14278
       grind)
    | exact superpose eq14278 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14278
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14278
       grind)
    | exact resolve eq13 eq14278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14278
  have eq14298 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14280
  have eq18245 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14298
       grind)
    | exact superpose eq14298 eq16
    | exact resolve eq16 eq14298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14298
  have eq18246 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18245
       have r₂ := eq22 x
       grind)
    | exact resolve eq18245 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18245
  have eq18260 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2811 x y
       have i₂ := eq18246
       grind)
    | exact superpose eq18246 eq2811
    | (have j0 := eq2811 x y
       grind)
    | exact resolve eq2811 eq18246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811 eq18246
  have eq18271 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18260
  have eq18272 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18271
  have eq18278 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18272
       grind)
    | exact superpose eq18272 eq16
    | exact resolve eq16 eq18272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18283 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq18272
       grind)
    | exact superpose eq18272 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18272
       grind)
    | exact resolve eq13 eq18272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18272
  have eq18301 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq18283
  have eq18302 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq18301
  have eq18308 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq18302
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18302
    | exact resolve eq18302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18302
  have eq18316 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18308
       grind)
    | exact superpose eq18308 eq10
    | exact resolve eq10 eq18308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18308
  have eq18380 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq18316
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18316
    | exact resolve eq18316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18316
  have eq18589 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18380
       grind)
    | exact superpose eq18380 eq16
    | exact resolve eq16 eq18380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18380
  have eq18590 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq18589
       have r₂ := eq22 x
       grind)
    | exact resolve eq18589 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18589
  have eq18601 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq18590
       grind)
    | exact superpose eq18590 eq10
    | exact resolve eq10 eq18590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18590
  have eq18666 : y = (k x y) := by
    first
    | (have i₁ := eq18601
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq18601
    | exact resolve eq18601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18601
  have eq18684 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4671 x y
       have i₂ := eq18666
       grind)
    | exact superpose eq18666 eq4671
    | (have j0 := eq4671 x y
       grind)
    | (have r₁ := eq4671 x y
       have r₂ := eq18666
       grind)
    | exact resolve eq4671 eq18666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671 eq18666
  have eq18693 : x = y ∨ y = (M.op x y) := by grind
  clear eq18684
  have eq18697 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18693
       grind)
    | exact superpose eq18693 eq16
    | exact resolve eq16 eq18693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18693
  have eq18702 : y = (M.op x y) := by
    first
    | (have r₁ := eq18697
       have r₂ := eq22 x
       grind)
    | exact resolve eq18697 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18697
  have eq18707 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18278
       have i₂ := eq18702
       grind)
    | exact superpose eq18702 eq18278
    | exact resolve eq18278 eq18702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18278 eq18702
  have eq18729 : (σ x) = (σ y) := by grind
  clear eq18707
  have eq18731 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18729
       grind)
    | exact superpose eq18729 eq10
    | exact resolve eq10 eq18729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18729
  have eq18795 : x = y := by
    first
    | (have i₁ := eq18731
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18731
    | exact resolve eq18731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18731
  have eq18799 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18795
       grind)
    | exact superpose eq18795 eq16
    | exact resolve eq16 eq18795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18795
  have eq18805 : False := by grind
  exact eq18805

/-- `Equation2919`: `x = ((y ◇ (x ◇ z)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pyx_Equation2919 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2919 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2919.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X2)) X0) X0) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op X0 (M.op x y)) x) x) := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) x x
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
  have eq69 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ x = (k y x) := by
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
  have eq70 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq120 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq117
  have eq121 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq120
  have eq160 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq211 : x = (M.op (M.op (M.op x y) x) x) := by
    first
    | (have i₁ := eq53 (M.op (M.op x (M.op sF0 x)) sF0)
       have i₂ := eq14 sF0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq214 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq54 (M.op (M.op x (M.op sF4 x)) sF4)
       have i₂ := eq14 sF4 x x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq638 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq75
  have eq720 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq638 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq9463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq9463
    | exact resolve eq9463 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9463
  have eq9475 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq9464
       have r₂ := eq28
       grind)
    | exact resolve eq9464 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9464
  have eq9479 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq9475
    | exact resolve eq9475 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9475
  have eq9484 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9479 eq70
    | (have r₁ := eq70
       have r₂ := eq9479
       grind)
    | exact resolve eq70 eq9479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq9479
  have eq9504 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq9484
  have eq9505 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq9504
  have eq9787 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9505 eq99
    | exact resolve eq99 eq9505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq9788 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9505 eq102
    | exact resolve eq102 eq9505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq9505
  have eq9800 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq9788
  have eq9811 : x = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq9787
    | exact resolve eq9787 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9787
  have eq9818 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq9811
       have r₂ := eq69
       grind)
    | exact resolve eq9811 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq9811
  have eq9821 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq9818
       grind)
    | exact superpose eq9818 eq87
    | exact resolve eq87 eq9818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq9830 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq720 x y
       have i₂ := eq9818
       grind)
    | exact superpose eq9818 eq720
    | (have j0 := eq720 x y
       grind)
    | exact resolve eq720 eq9818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq9818
  have eq9835 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9830
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq9830
    | exact resolve eq9830 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9830
  have eq9844 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9821
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9821
    | exact resolve eq9821 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9821
  have eq9847 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9835
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9835
    | exact resolve eq9835 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9835
  have eq9853 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9847
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq9847
    | exact resolve eq9847 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9847
  have eq9856 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9853
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9853
    | exact resolve eq9853 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9853
  have eq9859 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9856
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9856
    | exact resolve eq9856 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9856
  have eq9862 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq9859
    | exact resolve eq9859 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9859
  have eq9865 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9862
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9862
    | exact resolve eq9862 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9862
  have eq9870 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9865
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9865
    | exact resolve eq9865 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9865
  have eq9871 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9870
  have eq9887 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9844 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9844
  have eq9888 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9887
  have eq9892 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq9888
    | exact resolve eq9888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9888
  have eq9904 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq9892
    | exact resolve eq9892 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9892
  have eq10191 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq9800
       grind)
    | exact superpose eq9800 eq52
    | exact resolve eq52 eq9800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9800
  have eq10222 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq10191
    | exact resolve eq10191 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10191
  have eq10629 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9904 eq10222
    | exact resolve eq10222 eq9904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9904
  have eq10645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10629
  have eq10649 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq10645
       have r₂ := eq28
       grind)
    | exact resolve eq10645 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10645
  have eq10653 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10649 eq214
    | exact resolve eq214 eq10649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq10649
  have eq13816 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10653 eq56
    | exact resolve eq56 eq10653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10653
  have eq13856 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13816 eq10222
    | exact resolve eq10222 eq13816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10222 eq13816
  have eq13883 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13856
  have eq13908 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13883 eq30
    | exact resolve eq30 eq13883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14013 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq13908
    | exact resolve eq13908 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13908
  have eq14014 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq14013
  have eq14034 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq14014 eq29
    | exact resolve eq29 eq14014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14046 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq14014 eq68
    | exact resolve eq68 eq14014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14170 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq160 eq14046
    | exact resolve eq14046 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14046
  have eq14177 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq14034
    | exact resolve eq14034 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14034
  have eq14238 : x = (M.op (M.op x x) x) ∨ x = y := by
    first
    | exact superpose eq14177 eq211
    | exact resolve eq211 eq14177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq14177
  have eq15065 : x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq14238
       grind)
    | exact superpose eq14238 eq56
    | exact resolve eq56 eq14238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq14238
  have eq15210 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq15065
       grind)
    | exact superpose eq15065 eq52
    | exact resolve eq52 eq15065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15065
  have eq15264 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq15210
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15210
    | exact resolve eq15210 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15210
  have eq15337 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14014 eq15264
    | exact resolve eq15264 eq14014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14014 eq15264
  have eq15393 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq15337
  have eq15581 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq15393 eq160
    | exact resolve eq160 eq15393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq15393
  have eq15617 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31 eq15581
    | exact resolve eq15581 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15581
  have eq15780 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15617 eq14170
    | exact resolve eq14170 eq15617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14170 eq15617
  have eq15807 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq15780
  have eq15886 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq15807
       grind)
    | exact superpose eq15807 eq52
    | exact resolve eq52 eq15807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq15807
  have eq15938 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq15886
    | exact resolve eq15886 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15886
  have eq16321 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15938 eq9871
    | exact resolve eq9871 eq15938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9871 eq15938
  have eq16354 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16321
  have eq16362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16354
       have r₂ := eq13883
       grind)
    | exact resolve eq16354 eq13883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13883 eq16354
  have eq16373 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16362
       have r₂ := eq28
       grind)
    | exact resolve eq16362 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16362
  have eq16377 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq16373 eq30
    | exact resolve eq30 eq16373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16373
  have eq16498 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq16377
    | exact resolve eq16377 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16377
  have eq16499 : x = y := by grind
  clear eq16498
  have eq16650 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq16499
       grind)
    | exact superpose eq16499 eq19
    | exact resolve eq19 eq16499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq16651 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq16499
       grind)
    | exact superpose eq16499 eq25
    | exact resolve eq25 eq16499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16499
  have eq16753 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16651
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16651
    | exact resolve eq16651 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16651
  have eq16768 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16753 eq27
    | exact resolve eq27 eq16753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16753
  have eq17293 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq16768 eq68
    | exact resolve eq68 eq16768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq16768
  have eq17338 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17293
       have i₂ := eq16650
       grind)
    | exact superpose eq16650 eq17293
    | exact resolve eq17293 eq16650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16650 eq17293
  have eq17349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17338 eq15
    | exact resolve eq15 eq17338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17338
  have eq17395 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq17349
    | exact resolve eq17349 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17349
  have eq17404 : False := by grind
  exact eq17404

/-- `Equation2919`: `x = ((y ◇ (x ◇ z)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pyx_Equation2919 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2919 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2919.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X2)) X0) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq109 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op X0 X1)) X1
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq109
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X2) X0)) (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X2) X0) X1 X0
       have i₂ := eq109 X0 X2
       grind)
    | exact superpose eq109 eq9
    | exact resolve eq9 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq154 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq156 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq622 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq154 x y
       grind)
    | exact superpose eq154 eq16
    | (have j1 := eq154 x y
       grind)
    | exact resolve eq16 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq154 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq801 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq156 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq156
    | exact resolve eq156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq861 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq801 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq801
    | (have j0 := eq801 X0 X1
       grind)
    | exact resolve eq801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq920 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq628 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq628
    | (have j0 := eq628 (τ X1) (τ X0)
       grind)
    | exact resolve eq628 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq928 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq920 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq920
    | (have j0 := eq920 X0 X1
       grind)
    | exact resolve eq920 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq931 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq928 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq928
    | (have j0 := eq928 X0 X1
       grind)
    | exact resolve eq928 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq933 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq931 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq931
    | (have j0 := eq931 X0 X1
       grind)
    | exact resolve eq931 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq934 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq933 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq933
    | (have j0 := eq933 X0 X1
       grind)
    | exact resolve eq933 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq935 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq934 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq934
    | (have j0 := eq934 X0 X1
       grind)
    | exact resolve eq934 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq936 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq935 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq935
    | (have j0 := eq935 X0 X1
       grind)
    | exact resolve eq935 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq3886 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
       have i₂ := eq114 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq114 eq109
    | exact resolve eq109 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq3969 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq153 X0 X1
       grind)
    | exact superpose eq153 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq153 X0 X1
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq153 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X0)
       have r₂ := eq153 X0 (M.op (τ X0) X0)
       grind)
    | exact resolve eq13 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq3984 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3969 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3969
  have eq3985 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3984 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3984
  have eq3992 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3985 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq3985
    | (have j0 := eq3985 X0 X1
       grind)
    | exact resolve eq3985 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq3985
  have eq6730 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq622
       have i₂ := eq861 y x
       grind)
    | exact superpose eq861 eq622
    | (have j1 := eq861 (σ y) (σ x)
       grind)
    | (have r₁ := eq622
       have r₂ := eq861 y x
       grind)
    | (have r₁ := eq622
       have r₂ := eq861 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq622
       have r₂ := eq861 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq622 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq861
  have eq6731 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6730
  have eq6837 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6731
       grind)
    | exact superpose eq6731 eq16
    | exact resolve eq16 eq6731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6731
  have eq6838 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6837
       have r₂ := eq22 x
       grind)
    | exact resolve eq6837 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6837
  have eq6843 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq109 x y
       have i₂ := eq6838
       grind)
    | exact superpose eq6838 eq109
    | exact resolve eq109 eq6838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6856 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq109 (σ x) (σ y)
       have i₂ := eq6843
       grind)
    | exact superpose eq6843 eq109
    | exact resolve eq109 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq6843
  have eq6868 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq6856
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6856
    | exact resolve eq6856 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6856
  have eq27825 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6868
       grind)
    | exact superpose eq6868 eq10
    | exact resolve eq10 eq6868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6868
  have eq27897 : x = y ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq27825
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27825
    | exact resolve eq27825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27825
  have eq27899 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27897
       grind)
    | exact superpose eq27897 eq16
    | exact resolve eq16 eq27897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27897
  have eq27900 : (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op (M.op x x) x) := by
    first
    | (have r₁ := eq27899
       have r₂ := eq22 x
       grind)
    | exact resolve eq27899 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27899
  have eq27948 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq110 x
       have i₂ := eq27900
       grind)
    | exact superpose eq27900 eq110
    | exact resolve eq110 eq27900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq27900
  have eq28012 : x = (M.op (M.op x x) x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq27948
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq27948
    | exact resolve eq27948 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27948
  have eq28035 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3886 x x
       have i₂ := eq28012
       grind)
    | exact superpose eq28012 eq3886
    | exact resolve eq3886 eq28012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3886 eq28012
  have eq28101 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq28035
       grind)
    | exact superpose eq28035 eq10
    | exact resolve eq10 eq28035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28035
  have eq28174 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28101
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28101
    | exact resolve eq28101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28101
  have eq28175 : x = (M.op x x) := by grind
  clear eq28174
  have eq83105 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3992 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3992
    | (have j0 := eq3992 (M.op (σ X0) (σ X0)) (k X1 X0)
       grind)
    | exact resolve eq3992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq83288 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq83105 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq83105
    | (have j0 := eq83105 X0 X1
       grind)
    | exact resolve eq83105 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83105
  have eq83298 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83288 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq83288
    | (have j0 := eq83288 X0 X1
       grind)
    | exact resolve eq83288 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83288
  have eq83303 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83298 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq83298
    | (have j0 := eq83298 X0 X1
       grind)
    | exact resolve eq83298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83298
  have eq83548 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq83303 X0 X1
       grind)
    | exact superpose eq83303 eq10
    | (have j1 := eq83303 X0 X1
       grind)
    | exact resolve eq10 eq83303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83303
  have eq83654 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83548 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq83548
    | (have j0 := eq83548 X0 X1
       grind)
    | exact resolve eq83548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83548
  have eq84225 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83654 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83654
  have eq84464 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq84225 X0 x
       have i₂ := eq28175
       grind)
    | exact superpose eq28175 eq84225
    | (have j0 := eq84225 x (k X0 x)
       grind)
    | exact resolve eq84225 eq28175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84225
  have eq84495 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq84464 y
       have i₂ := eq6838
       grind)
    | exact superpose eq6838 eq84464
    | (have j0 := eq84464 y
       grind)
    | (have r₁ := eq84464 y
       have r₂ := eq6838
       grind)
    | exact resolve eq84464 eq6838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6838 eq84464
  have eq84508 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq84495
  have eq85595 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84508
       grind)
    | exact superpose eq84508 eq16
    | exact resolve eq16 eq84508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84508
  have eq85596 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq85595
       have r₂ := eq22 x
       grind)
    | exact resolve eq85595 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85595
  have eq85603 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq628 x y
       have i₂ := eq85596
       grind)
    | exact superpose eq85596 eq628
    | (have j0 := eq628 x y
       grind)
    | exact resolve eq628 eq85596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq85596
  have eq85633 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq85603
  have eq85634 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq85633
  have eq85642 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85634
       grind)
    | exact superpose eq85634 eq16
    | exact resolve eq16 eq85634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85653 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq85634
       grind)
    | exact superpose eq85634 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq85634
       grind)
    | exact resolve eq13 eq85634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85634
  have eq85698 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
  clear eq85653
  have eq85699 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
  clear eq85698
  have eq85722 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq85699
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq85699
    | exact resolve eq85699 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85699
  have eq85744 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq85722
       have i₂ := eq28175
       grind)
    | exact superpose eq28175 eq85722
    | exact resolve eq85722 eq28175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85722
  have eq85758 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq85744
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq85744
    | exact resolve eq85744 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85744
  have eq85789 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq85758
       grind)
    | exact superpose eq85758 eq10
    | exact resolve eq10 eq85758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85758
  have eq85894 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq85789
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq85789
    | exact resolve eq85789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85789
  have eq85898 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85894
       grind)
    | exact superpose eq85894 eq16
    | exact resolve eq16 eq85894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85894
  have eq85899 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq85898
       have r₂ := eq22 x
       grind)
    | exact resolve eq85898 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85898
  have eq85917 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq85899
       grind)
    | exact superpose eq85899 eq10
    | exact resolve eq10 eq85899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85899
  have eq86024 : x = (k y x) := by
    first
    | (have i₁ := eq85917
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq85917
    | exact resolve eq85917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85917
  have eq86047 : x ≠ x ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq936 y x
       have i₂ := eq86024
       grind)
    | exact superpose eq86024 eq936
    | (have j0 := eq936 y x
       grind)
    | (have r₁ := eq936 y x
       have r₂ := eq86024
       grind)
    | exact resolve eq936 eq86024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq86024
  have eq86066 : x = y ∨ x = (M.op x y) := by grind
  clear eq86047
  have eq86072 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86066
       grind)
    | exact superpose eq86066 eq16
    | exact resolve eq16 eq86066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86066
  have eq86077 : x = (M.op x y) := by
    first
    | (have r₁ := eq86072
       have r₂ := eq22 x
       grind)
    | exact resolve eq86072 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86072
  have eq86083 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq85642
       have i₂ := eq86077
       grind)
    | exact superpose eq86077 eq85642
    | exact resolve eq85642 eq86077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85642
  have eq86138 : (σ x) = (σ y) := by grind
  clear eq86083
  have eq86169 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86138
       grind)
    | exact superpose eq86138 eq16
    | exact resolve eq16 eq86138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86138
  have eq86276 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq86169
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq86169
    | exact resolve eq86169 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq86169
  have eq86278 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq86276
       have i₂ := eq28175
       grind)
    | exact superpose eq28175 eq86276
    | exact resolve eq86276 eq28175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28175 eq86276
  have eq86280 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq86278
       have i₂ := eq86077
       grind)
    | exact superpose eq86077 eq86278
    | exact resolve eq86278 eq86077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86077 eq86278
  have eq86281 : False := by grind
  exact eq86281

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_x_pyx_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq212 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op sF0 (M.op x X0)) x)
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq217 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op sF4 (M.op x X0)) x)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq481 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op X1 (M.op X2 X0)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X1) X1 X0
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X0 (M.op X0 X1) x
       have i₂ := eq56 X0 X0 X1 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq855 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) X3 X1
       have i₂ := eq56 X3 X1 X0 X2
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq1840 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq853 X0 (M.op X1 (M.op X2 X0))
       grind)
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq853 (M.op X1 (M.op X2 X0)) X0
       grind)
    | exact superpose eq853 eq481
    | exact resolve eq481 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1885 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq853 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq853 (M.op X1 X2) X0
       grind)
    | exact superpose eq853 eq491
    | exact resolve eq491 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2192 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq849 X0 X1 X2
       have i₂ := eq853 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | (have i₁ := eq849 X0 X1 X2
       have i₂ := eq853 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | exact superpose eq853 eq849
    | exact resolve eq849 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq2476 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2192 X1 X2 (M.op X1 (M.op X0 X2))
       have i₂ := eq1840 X2 X1 X0
       grind)
    | exact superpose eq1840 eq2192
    | exact resolve eq2192 eq1840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840 eq2192
  have eq2613 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X0
       have i₂ := eq853 X0 (M.op sF0 (M.op X0 X0))
       grind)
    | (have i₁ := eq212 X0 X1
       have i₂ := eq853 (M.op sF0 (M.op X1 X0)) X1
       grind)
    | exact superpose eq853 eq212
    | exact resolve eq212 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2698 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X0
       have i₂ := eq853 X0 (M.op sF4 (M.op X0 X0))
       grind)
    | (have i₁ := eq217 X0 X1
       have i₂ := eq853 (M.op sF4 (M.op X1 X0)) X1
       grind)
    | exact superpose eq853 eq217
    | exact resolve eq217 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq853
  have eq12509 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3))) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq855 X0 X1 X2 X3
       have i₂ := eq491 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq855 X0 X1 X2 X3
       have i₂ := eq491 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq491 eq855
    | exact resolve eq855 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq855
  have eq12510 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12509 X0 X1 X2 X3
       have i₂ := eq1885 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3)) X2
       grind)
    | exact superpose eq1885 eq12509
    | exact resolve eq12509 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885 eq12509
  have eq12511 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12510 X0 X1 X2 X3
       have i₂ := eq2476 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq12510 X0 X1 X2 X3
       have i₂ := eq2476 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq2476 eq12510
    | exact resolve eq12510 eq2476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2476 eq12510
  have eq39236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq39237 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq39236
    | exact resolve eq39236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39236
  have eq39248 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq39237
       have r₂ := eq28
       grind)
    | exact resolve eq39237 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39237
  have eq39252 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq39248
    | exact resolve eq39248 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39248
  have eq39324 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq39252 eq12511
    | exact resolve eq12511 eq39252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39252
  have eq39361 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq2698 eq39324
    | exact resolve eq39324 eq2698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698 eq39324
  have eq39362 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq39361
  have eq39487 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq12511 x x X1 X0
       have i₂ := eq39362
       grind)
    | exact superpose eq39362 eq12511
    | exact resolve eq12511 eq39362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12511 eq39362
  have eq39524 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2613 eq39487
    | exact resolve eq39487 eq2613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613 eq39487
  have eq39525 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq39524
  have eq39608 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq39525 eq30
    | exact resolve eq30 eq39525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39525
  have eq39745 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq39608
    | exact resolve eq39608 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq39608
  have eq39746 : x = y := by grind
  clear eq39745
  have eq39767 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq39746
       grind)
    | exact superpose eq39746 eq19
    | exact resolve eq19 eq39746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq39768 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39746
       grind)
    | exact superpose eq39746 eq25
    | exact resolve eq25 eq39746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq39746
  have eq39906 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq39768
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39768
    | exact resolve eq39768 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq39768
  have eq39925 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq39906 eq27
    | exact resolve eq27 eq39906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq39906
  have eq40307 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq39925 eq69
    | exact resolve eq69 eq39925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq39925
  have eq40454 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40307
       have i₂ := eq39767
       grind)
    | exact superpose eq39767 eq40307
    | exact resolve eq40307 eq39767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39767 eq40307
  have eq40493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40454 eq15
    | exact resolve eq15 eq40454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40454
  have eq40535 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq40493
    | exact resolve eq40493 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq40493
  have eq40544 : False := by grind
  exact eq40544

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq56 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq56 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq57 (σ X0)
       grind)
    | exact superpose eq57 eq15
    | exact resolve eq15 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq59
  have eq89 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq19 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq166 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 x (M.op X0 X0)
       have i₂ := eq133 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq133 eq9
    | exact resolve eq9 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq229 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq166 (σ X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq166
    | exact resolve eq166 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq166
  have eq260 : ∀ X0 X1 : G, (M.op (σ (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq229 (σ (M.op X0 X0)) X1
       have i₂ := eq229 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq229 eq229
    | exact resolve eq229 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq452 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq435 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq453 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq452 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq465 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq453 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq453 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq453 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq477 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq465
    | (have j0 := eq465 X0 X1
       grind)
    | exact resolve eq465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq478 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq477 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq546 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq478 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq478
    | exact resolve eq478 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq558 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq478 x y
       grind)
    | exact superpose eq478 eq16
    | exact resolve eq16 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq229 X1 (σ X0)
       have i₂ := eq478 (M.op X1 X1) X0
       grind)
    | exact superpose eq478 eq229
    | exact resolve eq229 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq478
  have eq698 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (M.op X1 X1))
       have i₂ := eq561 X0 X1
       grind)
    | exact superpose eq561 eq10
    | exact resolve eq10 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq717 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq698
    | exact resolve eq698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq784 : ∀ X0 X1 : G, (k X1 (σ (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq717 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq260 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq260 eq717
    | exact resolve eq717 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq717
  have eq943 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (σ (k X1 (k (τ X0) (σ (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 (σ (M.op X2 X2)) X1
       have i₂ := eq784 X2 X0
       grind)
    | exact superpose eq784 eq22
    | exact resolve eq22 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq954 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (k X0 (σ (σ (M.op X2 X2)))) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq943 X0 X1 X2
       have i₂ := eq546 X0 (σ (M.op X2 X2)) X1
       grind)
    | exact superpose eq546 eq943
    | exact resolve eq943 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq943
  have eq964 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq954 X0 X1 x
       have i₂ := eq784 x X0
       grind)
    | exact superpose eq784 eq954
    | exact resolve eq954 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq954
  have eq1106 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq964 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq964
    | exact resolve eq964 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1342 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq558
       have i₂ := eq1106 y x
       grind)
    | exact superpose eq1106 eq558
    | exact resolve eq558 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq1106
  have eq1343 : False := by grind
  exact eq1343

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq482 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq54 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq844 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ X2 = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq482 X1 X0 X3
       grind)
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq482 X0 X0 X2
       grind)
    | exact superpose eq482 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | (have r₁ := eq12 X2 (M.op X0 X0)
       have r₂ := eq482 X0 X0 X2
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X2
       have r₂ := eq482 X0 X0 X2
       grind)
    | exact resolve eq12 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X2 X3 : G, (M.op X2 X3) = (k X2 X3) ∨ X2 = X3 := by
    intro X2 X3
    first
    | (have j0 := eq844 x x X2 X3
       grind)
    | (have r₁ := eq844 x x X2 X3
       have r₂ := eq482 x x X2
       grind)
    | (have r₁ := eq844 x x (M.op x x) X3
       have r₂ := eq482 x x (M.op x x)
       grind)
    | exact resolve eq844 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq844
  have eq2577 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq887 x y
       grind)
    | exact superpose eq887 eq49
    | (have j1 := eq887 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2603 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2577
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2577
    | exact resolve eq2577 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq2604 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq2603
    | exact resolve eq2603 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2608 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2604 eq887
    | (have j0 := eq887 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq887 eq2604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq2604
  have eq2613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq2608
    | exact resolve eq2608 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2608
  have eq2616 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2613
       have r₂ := eq28
       grind)
    | exact resolve eq2613 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613
  have eq2619 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2616 eq30
    | exact resolve eq30 eq2616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2616
  have eq2636 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq2619
    | exact resolve eq2619 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2619
  have eq2637 : x = y := by grind
  clear eq2636
  have eq2795 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2637
       grind)
    | exact superpose eq2637 eq19
    | exact resolve eq19 eq2637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2796 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2637
       grind)
    | exact superpose eq2637 eq25
    | exact resolve eq25 eq2637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2637
  have eq2812 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2796
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2796
    | exact resolve eq2796 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2796
  have eq2815 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2812 eq27
    | exact resolve eq27 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2812
  have eq2893 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2815 eq66
    | exact resolve eq66 eq2815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2815
  have eq2937 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2893
       have i₂ := eq2795
       grind)
    | exact superpose eq2795 eq2893
    | exact resolve eq2893 eq2795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2795 eq2893
  have eq2938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2937 eq15
    | exact resolve eq15 eq2937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2937
  have eq2963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2938
    | exact resolve eq2938 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2938
  have eq2968 : False := by grind
  exact eq2968

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 X2 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq75 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq25 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X1
       have i₂ := eq25 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq25 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq25 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op (M.op X1 (M.op X2 X2)) X0) X3 X4 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op X1 X0) X4 X5 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1)
       have i₂ := eq24 X1 X2 X3 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 x (M.op X0 X0) X2
       have i₂ := eq25 x (M.op X0 X0) X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq203 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq40
    | (have j0 := eq40 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq774 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) X2)) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X2 X3 X4 X2
       have i₂ := eq75 X1 X0 X2
       grind)
    | (have i₁ := eq24 (M.op X1 X1) X1 X2 (M.op X0 X0)
       have i₂ := eq75 X0 X1 X2
       grind)
    | exact superpose eq75 eq24
    | exact resolve eq24 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1053 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X3)) (M.op (M.op X0 X0) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 X2 X3 (M.op X0 X0)
       have i₂ := eq82 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq83 X2 X3 (M.op X0 X0)
       have i₂ := eq82 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq82 eq83
    | exact resolve eq83 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq83
  have eq1273 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X3) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109 X0 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X3
       have i₂ := eq24 X0 X1 X2 X0
       grind)
    | exact superpose eq24 eq109
    | exact resolve eq109 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1592 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X1 (σ (M.op X0 X0)) (M.op X1 X1)
       have i₂ := eq74 X0 (M.op X1 X1) (σ (M.op X0 X0))
       grind)
    | exact superpose eq74 eq84
    | exact resolve eq84 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq84
  have eq6462 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op X2 (M.op X5 (M.op X6 X6)))) (M.op (M.op (M.op X7 X7) (M.op X8 X8)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2))) = X5 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq95 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op X2 (M.op X5 (M.op X6 X6)))) X5 X6 X7 X8
       have i₂ := eq97 (M.op X5 (M.op X6 X6)) X2 X0 X1 X3 X4
       grind)
    | exact superpose eq97 eq95
    | exact resolve eq95 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq97
  have eq6480 : ∀ X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op X2 (M.op X5 (M.op X6 X6)))) X2) = X5 := by
    intro X2 X3 X4 X5 X6
    first
    | (have i₁ := eq6462 x x X2 X3 X4 X5 X6 x x
       have i₂ := eq774 x x X2 x x
       grind)
    | exact superpose eq774 eq6462
    | exact resolve eq6462 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774 eq6462
  have eq14957 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op (M.op X2 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109 X2 X1 X1
       have i₂ := eq1592 X0 X1
       grind)
    | exact superpose eq1592 eq109
    | exact resolve eq109 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23623 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op X2 X2) (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109 X2 (σ X1) (σ X0)
       have i₂ := eq203 X1 X0
       grind)
    | exact superpose eq203 eq109
    | (have j1 := eq203 X1 X0
       grind)
    | exact resolve eq109 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq203
  have eq23896 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23623 X0 X1 x
       have i₂ := eq14957 X0 (σ X1) x
       grind)
    | exact superpose eq14957 eq23623
    | (have j0 := eq23623 X0 X1 x
       grind)
    | exact resolve eq23623 eq14957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14957 eq23623
  have eq23897 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq23896 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23896
  have eq337888 : ∀ X0 X3 X4 : G, (M.op X0 (M.op X3 (M.op X0 (M.op X4 X4)))) = X3 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1273 (M.op X3 (M.op X0 (M.op X4 X4))) x x X3
       have i₂ := eq6480 X3 x x X0 X4
       grind)
    | exact superpose eq6480 eq1273
    | exact resolve eq1273 eq6480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273 eq6480
  have eq346431 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq337888 (M.op X0 (M.op X1 X1)) X2 (M.op x x)
       have i₂ := eq1053 x x X0 X1
       grind)
    | exact superpose eq1053 eq337888
    | exact resolve eq337888 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053 eq337888
  have eq662468 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq23897 y x
       grind)
    | exact superpose eq23897 eq16
    | (have j1 := eq23897 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq23897 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq23897 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq23897 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq23897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23897
  have eq665465 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq662468
  have eq757141 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 X0)) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq346431 y X0 y
       have i₂ := eq665465
       grind)
    | exact superpose eq665465 eq346431
    | exact resolve eq346431 eq665465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665465
  have eq757145 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq757141 x
       have i₂ := eq346431 y x x
       grind)
    | exact superpose eq346431 eq757141
    | exact resolve eq757141 eq346431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346431 eq757141
  have eq757146 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq757145
  have eq854143 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq757146
       grind)
    | exact superpose eq757146 eq10
    | exact resolve eq10 eq757146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757146
  have eq854310 : x = y ∨ x = y := by
    first
    | (have i₁ := eq854143
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq854143
    | exact resolve eq854143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854143
  have eq854311 : x = y := by grind
  clear eq854310
  have eq909722 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq854311
       grind)
    | exact superpose eq854311 eq16
    | exact resolve eq16 eq854311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854311
  have eq909723 : False := by grind
  exact eq909723
