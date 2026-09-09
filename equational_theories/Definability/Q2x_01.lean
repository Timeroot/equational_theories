import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3716`: `x ◇ y = (x ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_x_x_pxy_pxx_Equation3716 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law3716 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3716.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq44 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X1 X2 X3 : G, (M.op X3 (M.op X1 X1)) = (M.op (M.op X3 X3) (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X1) (M.op X2 x)
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X1 X3 : G, (M.op X3 (M.op X1 X1)) = (M.op X3 X1) := by
    intro X1 X3
    first
    | (have i₁ := eq45 X1 x X3
       have i₂ := eq9 X3 X1 x
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1 x
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 x (M.op x x)
       have r₂ := eq47 x x
       grind)
    | exact resolve eq12 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X1 (M.op X2 X0)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq48
    | exact resolve eq48 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (σ X1) = (k (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq15
    | (have j1 := eq51 X0 X1
       grind)
    | exact resolve eq15 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq97 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) X2) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X1) X2
       have i₂ := eq52 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq52 eq13
    | (have j0 := eq13 (M.op X0 X1) X2
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq124 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq23
    | exact resolve eq23 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq128 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq124
    | exact resolve eq124 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq128 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq128
    | exact resolve eq128 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq130 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq129 (M.op X0 X1)
       have i₂ := eq52 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq52 eq129
    | exact resolve eq129 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op X0 X0) X0
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq23
    | exact resolve eq23 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq146 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq133 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133
    | exact resolve eq133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq14 (τ X0) (τ (M.op X0 X0))
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq14
    | (have j0 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq14 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq153 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq150 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq160 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = (M.op X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq146 X0
       grind)
    | exact superpose eq146 eq14
    | (have j0 := eq14 X0 X0
       grind)
    | exact resolve eq14 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq163 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op X0 (τ (M.op (σ X0) (σ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq160 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq182 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq130 X0 X0
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq130
    | exact resolve eq130 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq201 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq15
    | exact resolve eq15 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq284 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq14 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq201 X0
       grind)
    | exact superpose eq201 eq14
    | (have j0 := eq14 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       grind)
    | exact resolve eq14 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq287 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq284 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq337 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ (M.op X0 X0)) X1) = X1 ∨ (M.op (σ (M.op X0 X0)) X1) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) X1
       have i₂ := eq287 X0
       grind)
    | exact superpose eq287 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X0)) X1
       have r₂ := eq287 X0
       grind)
    | exact resolve eq13 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (k (σ (M.op X0 X0)) X1) ∨ (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq337 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq4716 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = X1 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X0 X1
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq97
    | (have j0 := eq97 X0 X0 X1
       grind)
    | (have r₁ := eq97 X0 X0 x
       have r₂ := eq48 X0 X0
       grind)
    | exact resolve eq97 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq4728 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq4716 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4716
  have eq4732 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4728 X0 X1
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq4728
    | (have j0 := eq4728 X0 X1
       grind)
    | exact resolve eq4728 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4728
  have eq4741 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4732 X0 X1
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq4732
    | (have j0 := eq4732 X0 X1
       grind)
    | exact resolve eq4732 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4732
  have eq4778 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (τ (M.op X0 X1)) = (k (τ (M.op X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (M.op X0 X0)
       have i₂ := eq4741 X0 X1
       grind)
    | exact superpose eq4741 eq23
    | (have j1 := eq4741 X0 X1
       grind)
    | exact resolve eq23 eq4741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4779 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (M.op X0 X1)) = (k (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq4741 X0 X1
       grind)
    | exact superpose eq4741 eq15
    | (have j1 := eq4741 X0 X1
       grind)
    | exact resolve eq15 eq4741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741
  have eq5254 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (k X0 X1) = X0 ∨ (τ (M.op X0 X1)) = (k (τ (M.op X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq4778 X0 X1
       grind)
    | exact superpose eq4778 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq4778 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq4778 X0 X1
       grind)
    | exact resolve eq12 eq4778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5257 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (k (τ (M.op X0 X0)) (τ X1)) ∨ (M.op X2 X0) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 X0
       have i₂ := eq4778 X0 X1
       grind)
    | exact superpose eq4778 eq52
    | (have j1 := eq4778 X0 X1
       grind)
    | exact resolve eq52 eq4778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5342 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ (M.op X0 X1)) = (k (τ (M.op X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5254 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5254
  have eq5530 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (σ (M.op X0 X0)) (σ X1)) ∨ (M.op X2 X0) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 X0
       have i₂ := eq4779 X0 X1
       grind)
    | exact superpose eq4779 eq52
    | (have j1 := eq4779 X0 X1
       grind)
    | exact resolve eq52 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5852 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (τ X1)) ∨ (τ (M.op X0 X1)) = (k (τ (M.op X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq5342 X0 X1
       grind)
    | exact superpose eq5342 eq23
    | (have j1 := eq5342 (τ X0) (τ X1)
       grind)
    | exact resolve eq23 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5342
  have eq6836 : ∀ X0 X1 X2 : G, (σ (τ (M.op X1 X2))) = (k (σ (τ (M.op X1 X1))) (σ (τ X2))) ∨ (M.op X0 X1) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (τ (M.op X1 X1)) (τ X2)
       have i₂ := eq5257 X1 X2 X0
       grind)
    | exact superpose eq5257 eq15
    | (have j1 := eq5257 X1 X2 X0
       grind)
    | exact resolve eq15 eq5257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5257
  have eq6845 : ∀ X0 X1 X2 : G, (σ (τ (M.op X1 X2))) = (k (σ (τ (M.op X1 X1))) X2) ∨ (M.op X0 X1) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6836 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq6836
    | (have j0 := eq6836 X0 X1 X2
       grind)
    | exact resolve eq6836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6836
  have eq6890 : ∀ X0 X1 X2 : G, (σ (τ (M.op X1 X2))) = (k (M.op X1 X1) X2) ∨ (M.op X0 X1) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6845 X0 X1 X2
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq6845
    | (have j0 := eq6845 X0 X1 X2
       grind)
    | exact resolve eq6845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845
  have eq6906 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X1) X2) ∨ (M.op X0 X1) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6890 X0 X1 X2
       have i₂ := eq11 (M.op X1 X2)
       grind)
    | exact superpose eq11 eq6890
    | (have j0 := eq6890 X0 X1 X2
       grind)
    | exact resolve eq6890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6890
  have eq7643 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ (M.op x x)) (σ y)) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq5530 x y X0
       grind)
    | exact superpose eq5530 eq16
    | (have j1 := eq5530 x y X0
       grind)
    | exact resolve eq16 eq5530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5530
  have eq11715 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 (τ (M.op X0 X0))) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (τ (M.op X0 X0)) X1 (τ X0)
       have i₂ := eq153 X0
       grind)
    | exact superpose eq153 eq52
    | (have j1 := eq153 X0
       grind)
    | exact resolve eq52 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq11781 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (τ (M.op (σ X0) (σ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11715 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11715
    | exact resolve eq11715 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11715
  have eq13326 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) (σ X0))) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5852 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5852
    | (have j0 := eq5852 (σ X0) X1
       grind)
    | exact resolve eq5852 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5852
  have eq15180 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11781 X0 X0
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq11781
    | (have j0 := eq11781 X0 x
       have j1 := eq163 X0
       grind)
    | exact resolve eq11781 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq11781
  have eq15232 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15180
  have eq15334 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq15232 X0
       grind)
    | exact superpose eq15232 eq11
    | (have j1 := eq15232 X0
       grind)
    | exact resolve eq11 eq15232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15232
  have eq32940 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op X2 X0) = (M.op X2 (τ X1)) ∨ (τ (M.op (σ (M.op X0 X0)) X1)) = (k (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6906 X2 X0 (τ X1)
       have i₂ := eq13326 (M.op X0 X0) X1
       grind)
    | exact superpose eq13326 eq6906
    | (have j0 := eq6906 X0 X0 (τ X1)
       have j1 := eq13326 (M.op X0 X0) X1
       grind)
    | exact resolve eq6906 eq13326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13326
  have eq32962 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ (M.op (σ (M.op X0 X0)) X1)) = (k (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq32940 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32940
  have eq32983 : ∀ X0 X1 : G, (τ (M.op (σ (M.op X0 X0)) X1)) = (k (τ (σ (M.op X0 X0))) (τ X1)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32962 X0 X1
       have i₂ := eq287 X0
       grind)
    | exact superpose eq287 eq32962
    | (have j0 := eq32962 X0 X1
       grind)
    | exact resolve eq32962 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32962
  have eq33038 : ∀ X0 X1 : G, (τ (M.op (σ (M.op X0 X0)) X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32983 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq32983
    | (have j0 := eq32983 X0 X1
       grind)
    | exact resolve eq32983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32983
  have eq76616 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (σ (k (M.op X0 X0) (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ (M.op X0 X0)) X1)
       have i₂ := eq33038 X0 X1
       grind)
    | exact superpose eq33038 eq11
    | (have j1 := eq33038 X0 X1
       grind)
    | exact resolve eq11 eq33038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33038
  have eq76830 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (k (σ (M.op X0 X0)) (σ (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76616 X0 X1
       have i₂ := eq15 (M.op X0 X0) (τ X1)
       grind)
    | exact superpose eq15 eq76616
    | (have j0 := eq76616 X0 X1
       grind)
    | exact resolve eq76616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76616
  have eq76903 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (k (σ (M.op X0 X0)) X1) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76830 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq76830
    | (have j0 := eq76830 X0 X1
       grind)
    | exact resolve eq76830 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76830
  have eq77076 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x x)) (σ y)) ∨ (M.op X0 x) = (M.op X0 y) ∨ (M.op x x) = (M.op x (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7643 X0
       have i₂ := eq76903 x (σ y)
       grind)
    | exact superpose eq76903 eq7643
    | (have j0 := eq7643 X0
       have j1 := eq76903 x (σ y)
       grind)
    | exact resolve eq7643 eq76903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7643 eq76903
  have eq77145 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x x)) (σ y)) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq77076 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq77076
    | (have j0 := eq77076 x
       grind)
    | exact resolve eq77076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77076
  have eq77146 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x x)) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq77145 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77145
  have eq79269 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq77146
       have i₂ := eq15334 x
       grind)
    | exact superpose eq15334 eq77146
    | (have j1 := eq15334 x
       grind)
    | exact resolve eq77146 eq15334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79302 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq79269
       have r₂ := eq48 (σ x) (σ y)
       grind)
    | exact resolve eq79269 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq79269
  have eq79314 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79302
       grind)
    | exact superpose eq79302 eq16
    | exact resolve eq16 eq79302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79318 : y ≠ (M.op x x) ∨ (M.op x x) = (k (M.op x x) y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq79302
       grind)
    | exact superpose eq79302 eq54
    | (have j0 := eq54 x y
       grind)
    | (have r₁ := eq54 x x
       have r₂ := eq79302
       grind)
    | exact resolve eq54 eq79302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq79370 : (τ (M.op x x)) = (k (τ (M.op x x)) (τ y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4778 x y
       have i₂ := eq79302
       grind)
    | exact superpose eq79302 eq4778
    | (have j0 := eq4778 x x
       grind)
    | exact resolve eq4778 eq79302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4778 eq79302
  have eq79562 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq79314
       have i₂ := eq15334 x
       grind)
    | exact superpose eq15334 eq79314
    | (have j1 := eq15334 x
       grind)
    | exact resolve eq79314 eq15334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79314
  have eq79569 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq79562
  have eq160026 : (σ (τ (M.op x x))) = (k (σ (τ (M.op x x))) (σ (τ y))) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15 (τ (M.op x x)) (τ y)
       have i₂ := eq79370
       grind)
    | exact superpose eq79370 eq15
    | exact resolve eq15 eq79370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79370
  have eq160039 : (σ (τ (M.op x x))) = (k (σ (τ (M.op x x))) y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq160026
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq160026
    | exact resolve eq160026 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160026
  have eq160047 : (M.op x x) = (k (M.op x x) y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq160039
       have i₂ := eq11 (M.op x x)
       grind)
    | exact superpose eq11 eq160039
    | exact resolve eq160039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160039
  have eq160051 : (M.op x x) = (k (M.op x x) y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq160047
       have r₂ := eq79318
       grind)
    | exact resolve eq160047 eq79318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79318 eq160047
  have eq160085 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15 (M.op x x) y
       have i₂ := eq160051
       grind)
    | exact superpose eq160051 eq15
    | exact resolve eq15 eq160051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160051
  have eq160118 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq160085
       have i₂ := eq15334 x
       grind)
    | exact superpose eq15334 eq160085
    | (have j1 := eq15334 x
       grind)
    | exact resolve eq160085 eq15334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15334 eq160085
  have eq160155 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq160118
  have eq160276 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6906 X0 (σ x) (σ y)
       have i₂ := eq160155
       grind)
    | exact superpose eq160155 eq6906
    | (have j0 := eq6906 (σ x) (σ y) (σ x)
       grind)
    | exact resolve eq6906 eq160155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6906 eq160155
  have eq160293 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq160276 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160276
  have eq160308 : x = (M.op x x) := by
    first
    | (have r₁ := eq160293
       have r₂ := eq79569
       grind)
    | exact resolve eq160293 eq79569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79569 eq160293
  have eq160361 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77146
       have i₂ := eq160308
       grind)
    | exact superpose eq160308 eq77146
    | exact resolve eq77146 eq160308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77146
  have eq160389 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq287 x
       have i₂ := eq160308
       grind)
    | exact superpose eq160308 eq287
    | exact resolve eq287 eq160308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq160395 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq348 x x
       have i₂ := eq160308
       grind)
    | exact superpose eq160308 eq348
    | exact resolve eq348 eq160308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq160641 : x = (M.op x y) := by grind
  clear eq160361
  have eq160772 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq160641
       grind)
    | exact superpose eq160641 eq16
    | exact resolve eq16 eq160641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160780 : x ≠ y ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq160641
       grind)
    | exact superpose eq160641 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq160641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160842 : x = y ∨ (σ x) = (k (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq4779 x y
       have i₂ := eq160641
       grind)
    | exact superpose eq160641 eq4779
    | exact resolve eq4779 eq160641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779 eq160641
  have eq160951 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq160842
       have i₂ := eq160308
       grind)
    | exact superpose eq160308 eq160842
    | exact resolve eq160842 eq160308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160308 eq160842
  have eq164329 : (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq23 (σ y) (σ x)
       have i₂ := eq160951
       grind)
    | exact superpose eq160951 eq23
    | exact resolve eq23 eq160951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq160951
  have eq164337 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = y := by
    first
    | (have i₁ := eq164329
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq164329
    | exact resolve eq164329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164329
  have eq164343 : x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq164337
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq164337
    | exact resolve eq164337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164337
  have eq164348 : x = (k x y) := by
    first
    | (have r₁ := eq164343
       have r₂ := eq160780
       grind)
    | exact resolve eq164343 eq160780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160780 eq164343
  have eq164375 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq164348
       grind)
    | exact superpose eq164348 eq15
    | exact resolve eq15 eq164348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164348
  have eq172182 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq160395 (σ y)
       have i₂ := eq164375
       grind)
    | exact superpose eq164375 eq160395
    | (have j0 := eq160395 (σ y)
       grind)
    | exact resolve eq160395 eq164375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160395 eq164375
  have eq172312 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq172182
       have r₂ := eq160772
       grind)
    | exact resolve eq172182 eq160772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172182
  have eq172355 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq52 (σ y) X0 (σ x)
       have i₂ := eq172312
       grind)
    | exact superpose eq172312 eq52
    | exact resolve eq52 eq172312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq172312
  have eq173151 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq160772
       have i₂ := eq172355 (σ x)
       grind)
    | exact superpose eq172355 eq160772
    | exact resolve eq160772 eq172355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160772 eq172355
  have eq173212 : False := by grind
  exact eq173212

/-- `Equation4389`: `x ◇ (x ◇ x) = (y ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pyx_y_pyx_Equation4389 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4389 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4389.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
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
  have eq24 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X2 X2) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 x X2
       have i₂ := eq9 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq9 X1 x
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
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X0 (M.op X0 X0)) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       have r₂ := eq9 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq70 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq72 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq70 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq70 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq70 (M.op X1 (k X1 X1)) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq75 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq71 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq71 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq118 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq75
    | exact resolve eq75 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq372 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq35 X0 (M.op X0 (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq478 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X0
       have i₂ := eq14 X0 (σ X0)
       grind)
    | (have i₁ := eq64 X0 X1
       have i₂ := eq14 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq9
    | (have j1 := eq64 X0 X0
       grind)
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq551 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq549 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq566 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq496 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq569 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq478 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq592 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq569 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq569 (M.op X1 (σ (k X1 X1))) X1
       have r₂ := eq12 (σ (k X1 X1)) X1
       grind)
    | (have r₁ := eq569 (M.op X1 (σ X1)) X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | (have r₁ := eq569 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq569 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq609 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq551 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq551
    | (have j0 := eq551 (τ X0)
       grind)
    | exact resolve eq551 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq612 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq609 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq609
    | (have j0 := eq609 X0
       grind)
    | exact resolve eq609 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq615 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq612 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq612
    | (have j0 := eq612 X0
       grind)
    | exact resolve eq612 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq1612 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq592
    | (have j0 := eq592 X1 (τ X0)
       grind)
    | exact resolve eq592 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq1700 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1612 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1612
    | (have j0 := eq1612 X0 X1
       grind)
    | exact resolve eq1612 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1612
  have eq1708 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1700 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1700
    | (have j0 := eq1700 X0 X1
       grind)
    | exact resolve eq1700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq1714 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1708 X0 X1
       have j1 := eq72 X1 X0
       grind)
    | (have r₁ := eq1708 X0 X1
       have r₂ := eq72 (k X0 X0) X1
       grind)
    | (have r₁ := eq1708 X0 X0
       have r₂ := eq72 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1708 X0 X1
       have r₂ := eq72 (k X1 X0) (M.op X0 X1)
       grind)
    | exact resolve eq1708 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1708
  have eq1750 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq615 X1
       have i₂ := eq1714 X1 X0
       grind)
    | (have i₁ := eq615 X0
       have i₂ := eq1714 X0 (k X0 X0)
       grind)
    | exact superpose eq1714 eq615
    | (have j0 := eq615 X1
       have j1 := eq1714 X1 X0
       grind)
    | (have r₁ := eq615 X1
       have r₂ := eq1714 X1 X1
       grind)
    | (have r₁ := eq615 (k X0 X0)
       have r₂ := eq1714 X0 (k (k X0 X0) (k X0 X0))
       grind)
    | exact resolve eq615 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq1776 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (σ X1)
       have i₂ := eq1714 (σ X1) X0
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq1714 X0 (k (σ X0) X1)
       grind)
    | exact superpose eq1714 eq31
    | (have j1 := eq1714 (σ X1) X0
       grind)
    | exact resolve eq31 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1826 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1776 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1776
    | (have j0 := eq1776 X0 X1
       grind)
    | exact resolve eq1776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776
  have eq1878 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1750 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1879 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1878 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1878 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq1878 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq2070 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1714 X0 X1
       have i₂ := eq1879 X0
       grind)
    | exact superpose eq1879 eq1714
    | (have j0 := eq1714 X0 X1
       grind)
    | exact resolve eq1714 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq2079 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1879 (σ X0)
       grind)
    | exact superpose eq1879 eq15
    | exact resolve eq15 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2098 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2079 X0
       have i₂ := eq1879 X0
       grind)
    | exact superpose eq1879 eq2079
    | exact resolve eq2079 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq2631 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq2098 X0
       grind)
    | exact superpose eq2098 eq9
    | exact resolve eq9 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10263 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1826 (σ X1) X0
       grind)
    | exact superpose eq1826 eq15
    | (have j1 := eq1826 (σ X1) X0
       grind)
    | exact resolve eq15 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq10286 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10263 X0 X1
       have i₂ := eq1879 X0
       grind)
    | exact superpose eq1879 eq10263
    | (have j0 := eq10263 X0 X1
       grind)
    | exact resolve eq10263 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10263
  have eq10387 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10286 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10286
    | (have j0 := eq10286 X0 X1
       grind)
    | exact resolve eq10286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10286
  have eq14523 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10387 x y
       grind)
    | exact superpose eq10387 eq16
    | (have j1 := eq10387 x y
       grind)
    | exact resolve eq16 eq10387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10387
  have eq14954 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14523
       have i₂ := eq2070 x y
       grind)
    | exact superpose eq2070 eq14523
    | (have j1 := eq2070 x y
       grind)
    | exact resolve eq14523 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070 eq14523
  have eq14961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq14954
  have eq14962 : y = (M.op x x) := by grind
  clear eq14961
  have eq15339 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq14962
       grind)
    | exact superpose eq14962 eq9
    | exact resolve eq9 eq14962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15342 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq24 X0 x
       have i₂ := eq14962
       grind)
    | exact superpose eq14962 eq24
    | exact resolve eq24 eq14962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq15344 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25 X0 x
       have i₂ := eq14962
       grind)
    | exact superpose eq14962 eq25
    | exact resolve eq25 eq14962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq15375 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2631 x X0
       have i₂ := eq14962
       grind)
    | exact superpose eq14962 eq2631
    | exact resolve eq2631 eq14962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14962
  have eq15392 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq15339 x
       have i₂ := eq15344 x
       grind)
    | exact superpose eq15344 eq15339
    | exact resolve eq15339 eq15344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15339
  have eq16004 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 (k X1 X1))) ∨ (σ (k X1 X1)) = (σ (k X1 (k X1 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq118 X1 (k X1 X1)
       have i₂ := eq566 X1 X0
       grind)
    | exact superpose eq566 eq118
    | (have j0 := eq118 X1 (k X1 X1)
       have j1 := eq566 X1 X1
       grind)
    | exact resolve eq118 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq566
  have eq16032 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 (M.op X1 X1))) ∨ (σ (k X1 X1)) = (σ (k X1 (k X1 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16004 X0 X1
       have i₂ := eq1879 X1
       grind)
    | exact superpose eq1879 eq16004
    | (have j0 := eq16004 X0 X1
       grind)
    | exact resolve eq16004 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16004
  have eq16102 : ∀ X1 : G, (M.op x y) = (σ (k X1 (M.op X1 X1))) ∨ (σ (k X1 X1)) = (σ (k X1 (k X1 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X1
    first
    | (have i₁ := eq16032 x X1
       have i₂ := eq15344 x
       grind)
    | exact superpose eq15344 eq16032
    | (have j0 := eq16032 x X1
       grind)
    | exact resolve eq16032 eq15344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16032
  have eq16138 : ∀ X1 : G, (σ (M.op X1 X1)) = (σ (k X1 (M.op X1 X1))) ∨ (M.op x y) = (σ (k X1 (M.op X1 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X1
    first
    | (have i₁ := eq16102 x
       have i₂ := eq1879 x
       grind)
    | exact superpose eq1879 eq16102
    | (have j0 := eq16102 X1
       grind)
    | exact resolve eq16102 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879 eq16102
  have eq16156 : ∀ X1 : G, (σ (M.op X1 X1)) = (σ (k X1 (M.op X1 X1))) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (M.op x y) = (σ (k X1 (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq16138 X1
       have i₂ := eq2098 X1
       grind)
    | exact superpose eq2098 eq16138
    | (have j0 := eq16138 X1
       grind)
    | exact resolve eq16138 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16138
  have eq16283 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq2631 X1 x
       have i₂ := eq15342 x
       grind)
    | exact superpose eq15342 eq2631
    | exact resolve eq2631 eq15342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631 eq15342
  have eq16317 : ∀ X1 : G, (M.op x y) = (M.op (σ X1) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq16283 X1
       have i₂ := eq15392
       grind)
    | exact superpose eq15392 eq16283
    | exact resolve eq16283 eq15392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15392 eq16283
  have eq16888 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq9 x X1
       have i₂ := eq15344 x
       grind)
    | exact superpose eq15344 eq9
    | exact resolve eq9 eq15344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21479 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16888 x
       have i₂ := eq15375 x
       grind)
    | exact superpose eq15375 eq16888
    | exact resolve eq16888 eq15375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15375 eq16888
  have eq22194 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21479
       grind)
    | exact superpose eq21479 eq16
    | exact resolve eq16 eq21479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21479
  have eq820867 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) ∨ (σ (M.op X0 (M.op X0 X0))) = (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) ∨ (M.op x y) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16156 (M.op X0 (M.op X0 X0))
       have i₂ := eq372 X0
       grind)
    | exact superpose eq372 eq16156
    | (have j0 := eq16156 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq16156 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq16156
  have eq821603 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) ∨ (M.op x y) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq820867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820867
  have eq821611 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq821603 X0
       have i₂ := eq15344 X0
       grind)
    | exact superpose eq15344 eq821603
    | (have j0 := eq821603 X0
       grind)
    | exact resolve eq821603 eq15344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821603
  have eq821613 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq821611 x
       have i₂ := eq15344 x
       grind)
    | exact superpose eq15344 eq821611
    | exact resolve eq821611 eq15344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15344 eq821611
  have eq821615 : (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq821613
       have r₂ := eq22194
       grind)
    | exact resolve eq821613 eq22194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821613
  have eq821678 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq16317 (M.op x y)
       have i₂ := eq821615
       grind)
    | exact superpose eq821615 eq16317
    | exact resolve eq16317 eq821615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16317
  have eq821694 : (M.op (M.op x y) (M.op x y)) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (M.op (M.op x y) (M.op x y))
       have i₂ := eq821615
       grind)
    | exact superpose eq821615 eq10
    | exact resolve eq10 eq821615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821615
  have eq821713 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq821694
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq821694
    | exact resolve eq821694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821694
  have eq821720 : (M.op x y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq821678
       have i₂ := eq2098 (M.op x y)
       grind)
    | exact superpose eq2098 eq821678
    | exact resolve eq821678 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098 eq821678
  have eq821758 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq821720
       have i₂ := eq821713
       grind)
    | exact superpose eq821713 eq821720
    | exact resolve eq821720 eq821713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821713 eq821720
  have eq821790 : False := by grind
  exact eq821790

/-- `Equation4389`: `x ◇ (x ◇ x) = (y ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyx_x_pyx_Equation4389 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4389 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4389.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq24 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X2 X2) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 x X2
       have i₂ := eq9 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq9 X1 x
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
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ X1 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X1 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op (M.op X1 X1) X1)
       have r₂ := eq9 (M.op (M.op X1 X1) X1) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq44 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44
    | (have j0 := eq44 X0
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq70 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq70 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq70 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq70 (M.op (k X1 X1) X0) X1
       have r₂ := eq12 X0 (k X1 X1)
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq367 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 (M.op (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq477 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X0
       have i₂ := eq14 (σ X0) X1
       grind)
    | (have i₁ := eq62 X0 X1
       have i₂ := eq14 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq10
    | (have j1 := eq62 X1 X0
       grind)
    | exact resolve eq10 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq549 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq547 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq567 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq477 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq590 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq567 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq567 (M.op (σ (k X1 X1)) X0) X1
       have r₂ := eq12 X0 (σ (k X1 X1))
       grind)
    | (have r₁ := eq567 (M.op (σ X1) X0) X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq567 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq567 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq607 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq549 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq549
    | (have j0 := eq549 (τ X0)
       grind)
    | exact resolve eq549 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq610 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq607 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq607
    | (have j0 := eq607 X0
       grind)
    | exact resolve eq607 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq613 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq610 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq610
    | (have j0 := eq610 X0
       grind)
    | exact resolve eq610 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq1612 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq590
    | (have j0 := eq590 X1 (τ X0)
       grind)
    | exact resolve eq590 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq1700 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1612 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1612
    | (have j0 := eq1612 X0 X1
       grind)
    | exact resolve eq1612 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1612
  have eq1708 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1700 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1700
    | (have j0 := eq1700 X0 X1
       grind)
    | exact resolve eq1700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq1714 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1708 X0 X1
       have j1 := eq72 X1 X0
       grind)
    | (have r₁ := eq1708 X0 X1
       have r₂ := eq72 (k X0 X0) X1
       grind)
    | (have r₁ := eq1708 X0 X0
       have r₂ := eq72 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1708 X0 X1
       have r₂ := eq72 (M.op X1 X0) (k X0 X1)
       grind)
    | exact resolve eq1708 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1708
  have eq1750 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X1
       have i₂ := eq1714 X1 X0
       grind)
    | (have i₁ := eq613 X0
       have i₂ := eq1714 X0 (k X0 X0)
       grind)
    | exact superpose eq1714 eq613
    | (have j0 := eq613 X1
       have j1 := eq1714 X1 X0
       grind)
    | (have r₁ := eq613 X1
       have r₂ := eq1714 X1 X1
       grind)
    | (have r₁ := eq613 (k X0 X0)
       have r₂ := eq1714 X0 (k (k X0 X0) (k X0 X0))
       grind)
    | exact resolve eq613 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq1776 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ (σ X1))) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (σ X1)
       have i₂ := eq1714 (σ X1) X0
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq1714 X0 (k (σ X0) X1)
       grind)
    | exact superpose eq1714 eq31
    | (have j1 := eq1714 (σ X1) X0
       grind)
    | exact resolve eq31 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1826 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1776 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1776
    | (have j0 := eq1776 X0 X1
       grind)
    | exact resolve eq1776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776
  have eq1879 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1750 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1880 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1879 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1879 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq1879 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq2071 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1714 X0 X1
       have i₂ := eq1880 X0
       grind)
    | exact superpose eq1880 eq1714
    | (have j0 := eq1714 X0 X1
       grind)
    | exact resolve eq1714 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq2080 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1880 (σ X0)
       grind)
    | exact superpose eq1880 eq15
    | exact resolve eq15 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2086 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq1880 (τ X0)
       grind)
    | exact superpose eq1880 eq36
    | exact resolve eq36 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq2093 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2086 X0
       have i₂ := eq1880 X0
       grind)
    | exact superpose eq1880 eq2086
    | exact resolve eq2086 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086
  have eq2099 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2080 X0
       have i₂ := eq1880 X0
       grind)
    | exact superpose eq1880 eq2080
    | exact resolve eq2080 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq2350 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq2093 X0
       grind)
    | exact superpose eq2093 eq9
    | exact resolve eq9 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2354 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq2093 X0
       grind)
    | exact superpose eq2093 eq24
    | exact resolve eq24 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2637 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (σ X0)
       have i₂ := eq2099 X0
       grind)
    | exact superpose eq2099 eq24
    | exact resolve eq24 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2639 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (σ X0)
       have i₂ := eq2099 X0
       grind)
    | exact superpose eq2099 eq25
    | exact resolve eq25 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq10438 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1826 (σ X0) X1
       grind)
    | exact superpose eq1826 eq15
    | (have j1 := eq1826 (σ X0) X1
       grind)
    | exact resolve eq15 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq10486 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10438 X0 X1
       have i₂ := eq1880 X1
       grind)
    | exact superpose eq1880 eq10438
    | (have j0 := eq10438 X0 X1
       grind)
    | exact resolve eq10438 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880 eq10438
  have eq10582 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10486 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10486
    | (have j0 := eq10486 X0 X1
       grind)
    | exact resolve eq10486 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10486
  have eq14524 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10582 x y
       grind)
    | exact superpose eq10582 eq16
    | (have j1 := eq10582 x y
       grind)
    | exact resolve eq16 eq10582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10582
  have eq14951 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14524
       have i₂ := eq2071 y x
       grind)
    | exact superpose eq2071 eq14524
    | (have j1 := eq2071 y x
       grind)
    | exact resolve eq14524 eq2071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071 eq14524
  have eq14958 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq14951
  have eq14959 : x = (M.op y y) := by grind
  clear eq14958
  have eq15336 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq14959
       grind)
    | exact superpose eq14959 eq9
    | exact resolve eq9 eq14959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15339 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24 X0 y
       have i₂ := eq14959
       grind)
    | exact superpose eq14959 eq24
    | exact resolve eq24 eq14959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq15369 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (τ x) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq2350 y X0
       have i₂ := eq14959
       grind)
    | exact superpose eq14959 eq2350
    | exact resolve eq2350 eq14959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq15370 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (τ x) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq2354 y X0
       have i₂ := eq14959
       grind)
    | exact superpose eq14959 eq2354
    | exact resolve eq2354 eq14959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq15374 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2637 y X0
       have i₂ := eq14959
       grind)
    | exact superpose eq14959 eq2637
    | exact resolve eq2637 eq14959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637 eq14959
  have eq15388 : (M.op (σ x) (σ y)) = (M.op (τ x) (τ y)) := by
    first
    | (have i₁ := eq15370 x
       have i₂ := eq15374 x
       grind)
    | exact superpose eq15374 eq15370
    | exact resolve eq15370 eq15374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15370
  have eq15878 : ∀ X1 : G, (M.op x y) = (M.op (σ X1) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq2639 X1 x
       have i₂ := eq15336 x
       grind)
    | exact superpose eq15336 eq2639
    | exact resolve eq2639 eq15336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15336
  have eq19240 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (τ x) (τ y)) := by
    intro X1
    first
    | (have i₁ := eq2639 X1 x
       have i₂ := eq15369 x
       grind)
    | exact superpose eq15369 eq2639
    | exact resolve eq2639 eq15369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639 eq15369
  have eq19323 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ X1) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq19240 X1
       have i₂ := eq15388
       grind)
    | exact superpose eq15388 eq19240
    | exact resolve eq19240 eq15388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15388 eq19240
  have eq19406 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19323 x
       have i₂ := eq15878 x
       grind)
    | exact superpose eq15878 eq19323
    | exact resolve eq19323 eq15878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19323
  have eq20445 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19406
       grind)
    | exact superpose eq19406 eq16
    | exact resolve eq16 eq19406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20550 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq367 x
       have i₂ := eq15339 x
       grind)
    | exact superpose eq15339 eq367
    | exact resolve eq367 eq15339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15339
  have eq22555 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) ∨ (M.op (τ (τ X0)) (τ (τ X0))) = (M.op (M.op (τ (τ X0)) (τ (τ X0))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | (have j1 := eq45 (τ X0)
       grind)
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq22569 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (τ (M.op (τ X0) (τ X0)))))) ∨ (M.op (τ (τ X0)) (τ (τ X0))) = (M.op (M.op (τ (τ X0)) (τ (τ X0))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22555 X0
       have i₂ := eq2093 (τ X0)
       grind)
    | exact superpose eq2093 eq22555
    | (have j0 := eq22555 X0
       grind)
    | exact resolve eq22555 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22555
  have eq22682 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (τ (τ X0)) (τ (τ X0))) = (M.op (M.op (τ (τ X0)) (τ (τ X0))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22569 X0
       have i₂ := eq11 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq11 eq22569
    | (have j0 := eq22569 X0
       grind)
    | exact resolve eq22569 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22569
  have eq22792 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (M.op (τ (τ X0)) (τ (τ X0))) = (M.op (M.op (τ (τ X0)) (τ (τ X0))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22682 X0
       have i₂ := eq2093 X0
       grind)
    | exact superpose eq2093 eq22682
    | (have j0 := eq22682 X0
       grind)
    | exact resolve eq22682 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22682
  have eq22896 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op (τ (τ X0)) (τ (τ X0))) = (M.op (M.op (τ (τ X0)) (τ (τ X0))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22792 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq22792
    | (have j0 := eq22792 X0
       grind)
    | exact resolve eq22792 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22792
  have eq22996 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (τ (τ X0)) (τ (τ X0))) = (M.op (M.op (τ (τ X0)) (τ (τ X0))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22896 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22896
    | (have j0 := eq22896 X0
       grind)
    | exact resolve eq22896 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22896
  have eq23091 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22996 X0
       have i₂ := eq15374 (τ (τ X0))
       grind)
    | exact superpose eq15374 eq22996
    | (have j0 := eq22996 X0
       grind)
    | exact resolve eq22996 eq15374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22996
  have eq23165 : ∀ X0 : G, (M.op (σ x) (σ y)) = (τ (M.op (τ X0) (τ X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23091 X0
       have i₂ := eq2093 (τ X0)
       grind)
    | exact superpose eq2093 eq23091
    | (have j0 := eq23091 X0
       grind)
    | exact resolve eq23091 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23091
  have eq23217 : ∀ X0 : G, (M.op (σ x) (σ y)) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23165 X0
       have i₂ := eq2093 X0
       grind)
    | exact superpose eq2093 eq23165
    | (have j0 := eq23165 X0
       grind)
    | exact resolve eq23165 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23165
  have eq23255 : ∀ X0 : G, (M.op x y) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23217 X0
       have i₂ := eq19406
       grind)
    | exact superpose eq19406 eq23217
    | (have j0 := eq23217 X0
       grind)
    | exact resolve eq23217 eq19406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23217
  have eq28908 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq512 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq28911 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28908 X0 X1
       have i₂ := eq2099 X1
       grind)
    | exact superpose eq2099 eq28908
    | (have j0 := eq28908 X0 X1
       grind)
    | exact resolve eq28908 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28908
  have eq29063 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28911 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq28911
    | (have j0 := eq28911 X0 X1
       grind)
    | exact resolve eq28911 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28911
  have eq105419 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (τ (M.op X0 X0))
       have i₂ := eq23255 X0
       grind)
    | exact superpose eq23255 eq11
    | (have j1 := eq23255 X0
       grind)
    | exact resolve eq11 eq23255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212938 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) ∨ (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq29063 (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       have i₂ := eq367 X0
       grind)
    | exact superpose eq367 eq29063
    | (have j0 := eq29063 (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact resolve eq29063 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq29063
  have eq213048 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) ∨ (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have j0 := eq212938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212938
  have eq213127 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq213048 X0
       have i₂ := eq15374 X0
       grind)
    | exact superpose eq15374 eq213048
    | (have j0 := eq213048 X0
       grind)
    | exact resolve eq213048 eq15374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213048
  have eq213176 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq213127 X0
       have i₂ := eq19406
       grind)
    | exact superpose eq19406 eq213127
    | (have j0 := eq213127 X0
       grind)
    | exact resolve eq213127 eq19406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213127
  have eq213210 : ∀ X0 : G, (M.op x y) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq213176 X0
       have i₂ := eq15878 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq15878 eq213176
    | exact resolve eq213176 eq15878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213176
  have eq213221 : (M.op x y) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq213210 x
       have i₂ := eq15374 x
       grind)
    | exact superpose eq15374 eq213210
    | exact resolve eq213210 eq15374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15374 eq213210
  have eq213223 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq213221
       have i₂ := eq19406
       grind)
    | exact superpose eq19406 eq213221
    | exact resolve eq213221 eq19406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19406 eq213221
  have eq213224 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq213223
       have r₂ := eq20445
       grind)
    | exact resolve eq213223 eq20445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213223
  have eq305934 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (M.op x y)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq105419 (τ X0)
       grind)
    | exact superpose eq105419 eq18
    | (have j1 := eq105419 (τ X0)
       grind)
    | exact resolve eq18 eq105419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq105419
  have eq305956 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (σ (M.op x y)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq305934 X0
       have i₂ := eq2093 X0
       grind)
    | exact superpose eq2093 eq305934
    | (have j0 := eq305934 X0
       grind)
    | exact resolve eq305934 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305934
  have eq305984 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (σ (M.op x y)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq305956 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq305956
    | (have j0 := eq305956 X0
       grind)
    | exact resolve eq305956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305956
  have eq306002 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (M.op x y)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq305984 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq305984
    | (have j0 := eq305984 X0
       grind)
    | exact resolve eq305984 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305984
  have eq306018 : ∀ X0 : G, (σ (M.op x y)) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq306002 X0
       have i₂ := eq2093 X0
       grind)
    | exact superpose eq2093 eq306002
    | (have j0 := eq306002 X0
       grind)
    | exact resolve eq306002 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093 eq306002
  have eq972238 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23255 X0
       have i₂ := eq306018 X0
       grind)
    | exact superpose eq306018 eq23255
    | (have j0 := eq23255 X0
       have j1 := eq306018 X0
       grind)
    | exact resolve eq23255 eq306018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23255 eq306018
  have eq972252 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq972238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972238
  have eq972257 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq972252 X0
       grind)
    | (have r₁ := eq972252 X0
       have r₂ := eq20445
       grind)
    | exact resolve eq972252 eq20445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972252
  have eq6070526 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq972257 (M.op (M.op x y) (M.op x y))
       have i₂ := eq213224
       grind)
    | exact superpose eq213224 eq972257
    | exact resolve eq972257 eq213224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213224 eq972257
  have eq6070527 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq6070526
       have i₂ := eq20550
       grind)
    | exact superpose eq20550 eq6070526
    | exact resolve eq6070526 eq20550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20550 eq6070526
  have eq6070659 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq15878 (M.op x y)
       have i₂ := eq6070527
       grind)
    | exact superpose eq6070527 eq15878
    | exact resolve eq15878 eq6070527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15878
  have eq6070742 : (M.op x y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq6070659
       have i₂ := eq2099 (M.op x y)
       grind)
    | exact superpose eq2099 eq6070659
    | exact resolve eq6070659 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099 eq6070659
  have eq6070842 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq6070742
       have i₂ := eq6070527
       grind)
    | exact superpose eq6070527 eq6070742
    | exact resolve eq6070742 eq6070527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6070527 eq6070742
  have eq6070895 : False := by grind
  exact eq6070895

/-- `Equation823`: `x = x ◇ ((x ◇ y) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pxy_pyx_Equation823 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law823 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law823.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq29
    | (have j0 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq38 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq67 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq34 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10
    | (have j1 := eq34 X1 X0
       grind)
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq263 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq249
    | (have j0 := eq249 X0 X1
       grind)
    | exact resolve eq249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq1124 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38
    | exact resolve eq38 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1229 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1124 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1124
    | (have j0 := eq1124 X0 X1
       grind)
    | exact resolve eq1124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1695 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq263 y x
       grind)
    | exact superpose eq263 eq16
    | (have j1 := eq263 y x
       grind)
    | exact resolve eq16 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq9425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1695
       have i₂ := eq1229 y x
       grind)
    | exact superpose eq1229 eq1695
    | (have j1 := eq1229 y x
       grind)
    | (have r₁ := eq1695
       have r₂ := eq1229 y x
       grind)
    | (have r₁ := eq1695
       have r₂ := eq1229 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1695
       have r₂ := eq1229 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1695 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229 eq1695
  have eq9430 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9425
  have eq9431 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9430
  have eq10061 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25 x
       have i₂ := eq9431
       grind)
    | exact superpose eq9431 eq25
    | exact resolve eq25 eq9431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq10064 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67 x
       have i₂ := eq9431
       grind)
    | exact superpose eq9431 eq67
    | exact resolve eq67 eq9431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq9431
  have eq21644 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq10064
       grind)
    | exact superpose eq10064 eq16
    | exact resolve eq16 eq10064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10064
  have eq21854 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21644
       have i₂ := eq10061
       grind)
    | exact superpose eq10061 eq21644
    | exact resolve eq21644 eq10061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10061 eq21644
  have eq21864 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21854
  have eq21865 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq21864
  have eq22306 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21865
       grind)
    | exact superpose eq21865 eq10
    | exact resolve eq10 eq21865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21865
  have eq22393 : x = y ∨ x = y := by
    first
    | (have i₁ := eq22306
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22306
    | exact resolve eq22306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22306
  have eq22394 : x = y := by grind
  clear eq22393
  have eq22841 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22394
       grind)
    | exact superpose eq22394 eq16
    | exact resolve eq16 eq22394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22394
  have eq22842 : False := by grind
  exact eq22842

/-- `Equation844`: `x = x ◇ ((y ◇ y) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_x_x_pyx_Equation844 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law844 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law844.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20
    | exact resolve eq20 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq48 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  clear eq29
  have eq58 : ∀ X1 X2 : G, (M.op X2 X2) = (M.op (M.op X2 X2) (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) X1 (M.op (M.op X1 X1) x)
       have i₂ := eq9 (M.op X1 X1) X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X1
       have i₂ := eq58 X1 X0
       grind)
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq79 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19
    | exact resolve eq19 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq100 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq14
    | (have j0 := eq14 (τ (M.op X0 X0)) (M.op (τ X0) (τ (M.op X0 X0)))
       grind)
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq102 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq126 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq14 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact superpose eq14 eq79
    | (have j1 := eq14 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact resolve eq79 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq145 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq102 y x
       grind)
    | exact superpose eq102 eq16
    | (have j1 := eq102 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq102 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq102 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq239 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq145
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq145
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq145
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq145
       have r₂ := eq14 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq145
       have r₂ := eq14 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq145 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq240 : x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq239
  have eq241 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq240
       grind)
    | exact superpose eq240 eq16
    | exact resolve eq16 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq1599 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 X1) (σ (M.op X0 X0)))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ (M.op X0 X0))
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq9
    | (have j1 := eq99 X0
       grind)
    | exact resolve eq9 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq3109 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (σ (M.op (τ X0) (τ X0))))) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1599 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1599
    | exact resolve eq1599 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq7622 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))) ∨ (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3109 (M.op X0 X0) X0
       have i₂ := eq126 (M.op X0 X0)
       grind)
    | exact superpose eq126 eq3109
    | (have j0 := eq3109 (M.op X0 X0) x
       have j1 := eq126 (M.op X0 X0)
       grind)
    | exact resolve eq3109 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3109
  have eq7661 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))) ∨ (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq7622 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7622
  have eq7704 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))) ∨ (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq7661 X0
       have i₂ := eq65 X0 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq7661
    | (have j0 := eq7661 X0
       grind)
    | exact resolve eq7661 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7661
  have eq7705 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))) ∨ (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq7704 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7704
  have eq7731 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq126 (M.op X0 X0)
       have i₂ := eq7705 X0
       grind)
    | exact superpose eq7705 eq126
    | (have j0 := eq126 (M.op X0 X0)
       have j1 := eq7705 X0
       grind)
    | exact resolve eq126 eq7705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7705
  have eq7739 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq7731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7731
  have eq7748 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq7739 X0
       have i₂ := eq65 X0 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq7739
    | (have j0 := eq7739 X0
       grind)
    | exact resolve eq7739 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7739
  have eq7749 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq7748 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7748
  have eq7797 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))
       have i₂ := eq7749 X0
       grind)
    | exact superpose eq7749 eq10
    | exact resolve eq10 eq7749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7749
  have eq7917 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (τ (M.op X0 X0)) X1
       have i₂ := eq7797 X0
       grind)
    | exact superpose eq7797 eq65
    | exact resolve eq65 eq7797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7797
  have eq8061 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq100 X0
       have i₂ := eq7917 X0 (τ X0)
       grind)
    | exact superpose eq7917 eq100
    | (have j0 := eq100 X0
       grind)
    | exact resolve eq100 eq7917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq7917
  have eq8062 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8061 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8061
  have eq11148 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq8062 X0
       grind)
    | exact superpose eq8062 eq11
    | (have j1 := eq8062 X0
       grind)
    | exact resolve eq11 eq8062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11189 : ∀ X0 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8062
  have eq11869 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11189 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11189
    | exact resolve eq11189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11189
  have eq11895 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11869 (M.op X0 X0)
       have i₂ := eq65 X0 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq11869
    | (have j0 := eq11869 (M.op X0 X0)
       grind)
    | (have r₁ := eq11869 (M.op X0 X0)
       have r₂ := eq65 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11869 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11869
  have eq11916 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq11895 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11895
  have eq11997 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       have i₂ := eq11916 X0
       grind)
    | exact superpose eq11916 eq11
    | exact resolve eq11 eq11916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11916
  have eq12078 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ (M.op X0 X0)) X1
       have i₂ := eq11997 X0
       grind)
    | exact superpose eq11997 eq65
    | exact resolve eq65 eq11997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11997
  have eq12214 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq126 X0
       have i₂ := eq12078 (τ X0) X0
       grind)
    | exact superpose eq12078 eq126
    | (have j0 := eq126 X0
       grind)
    | exact resolve eq126 eq12078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq12078
  have eq12258 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq12214 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12214
  have eq17424 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11148 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11148
    | exact resolve eq11148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11148
  have eq25216 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12258 (M.op (σ X0) (σ X0))
       have i₂ := eq17424 X0
       grind)
    | exact superpose eq17424 eq12258
    | (have j1 := eq17424 X0
       grind)
    | exact resolve eq12258 eq17424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12258 eq17424
  have eq25360 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq25216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25216
  have eq25404 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25360 X0
       have i₂ := eq65 (σ X0) (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq65 eq25360
    | (have j0 := eq25360 X0
       grind)
    | exact resolve eq25360 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25360
  have eq25405 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq25404 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25404
  have eq25429 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq241
       have r₂ := eq25405 x
       grind)
    | exact resolve eq241 eq25405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq25553 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq25405 X0
       grind)
    | exact superpose eq25405 eq10
    | exact resolve eq10 eq25405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25991 : y = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25429
       grind)
    | exact superpose eq25429 eq10
    | exact resolve eq10 eq25429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25429
  have eq26030 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25991
       have i₂ := eq25553 x
       grind)
    | exact superpose eq25553 eq25991
    | exact resolve eq25991 eq25553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25553 eq25991
  have eq26031 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq26030
  have eq26066 : y = (τ (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26031
       grind)
    | exact superpose eq26031 eq10
    | exact resolve eq10 eq26031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26031
  have eq26091 : x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26066
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26066
    | exact resolve eq26066 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26066
  have eq26093 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26091
       grind)
    | exact superpose eq26091 eq16
    | exact resolve eq16 eq26091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26091
  have eq26094 : y = (M.op x x) := by
    first
    | (have r₁ := eq26093
       have r₂ := eq25405 x
       grind)
    | exact resolve eq26093 eq25405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26093
  have eq26098 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 x X0
       have i₂ := eq26094
       grind)
    | exact superpose eq26094 eq65
    | exact resolve eq65 eq26094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26155 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25405 x
       have i₂ := eq26094
       grind)
    | exact superpose eq26094 eq25405
    | exact resolve eq25405 eq26094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25405 eq26094
  have eq26264 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26098 x
       grind)
    | exact superpose eq26098 eq16
    | exact resolve eq16 eq26098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26098
  have eq26352 : (σ x) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq26264
       have i₂ := eq26155
       grind)
    | exact superpose eq26155 eq26264
    | exact resolve eq26264 eq26155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26155 eq26264
  have eq26379 : False := by grind
  exact eq26379
