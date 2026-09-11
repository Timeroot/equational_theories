import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation838 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq116 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq117 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq118 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq119 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq653 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq117 x y
       grind)
    | exact superpose eq117 eq16
    | (have j1 := eq117 x y
       grind)
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq117 X1 X0
       grind)
    | exact superpose eq117 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq117 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq117 X0 X1
       grind)
    | exact resolve eq13 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq664 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq660 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq667 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq664 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq664 X0 X1
       have r₂ := eq13 (σ X0) (σ (k X0 X1))
       grind)
    | (have r₁ := eq664 X0 X1
       have r₂ := eq13 (σ (k X0 X1)) (σ X0)
       grind)
    | (have r₁ := eq664 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq664 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq676 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq667 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq667
    | (have j0 := eq667 X0 X1
       grind)
    | exact resolve eq667 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq681 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq676
    | (have j0 := eq676 X0 X1
       grind)
    | exact resolve eq676 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq834 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq895 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq834 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq834
    | (have j0 := eq834 X0 X1
       grind)
    | exact resolve eq834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq4094 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq119 X1 X0
       grind)
    | exact superpose eq119 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq119 X1 X0
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq119 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq119 (M.op X1 (τ X1)) X1
       grind)
    | exact resolve eq13 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq4107 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4094 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094
  have eq4108 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4107
  have eq4117 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4108 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq4108
    | (have j0 := eq4108 X0 X1
       grind)
    | exact resolve eq4108 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq4108
  have eq4154 : ∀ X0 X1 : G, (σ X0) ≠ (k (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) ∨ (σ X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq681 X1 (τ X0)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq681
    | (have j0 := eq681 X0 (τ X1)
       grind)
    | exact resolve eq681 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq4180 : ∀ X0 X1 : G, (σ X0) ≠ (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4154 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4154
    | (have j0 := eq4154 X0 X1
       grind)
    | exact resolve eq4154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4154
  have eq4421 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq118 X1 X0
       grind)
    | exact superpose eq118 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq118 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq118 (M.op X1 (σ X1)) X1
       grind)
    | exact resolve eq13 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq4435 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4421 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4421
  have eq4436 : ∀ X0 X1 : G, (σ X0) = X1 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4435 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4435
  have eq4447 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4436 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq4436
    | (have j0 := eq4436 X0 X1
       grind)
    | exact resolve eq4436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4436
  have eq6814 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq653
       have i₂ := eq895 x y
       grind)
    | exact superpose eq895 eq653
    | (have j1 := eq895 (σ x) (σ y)
       grind)
    | (have r₁ := eq653
       have r₂ := eq895 x y
       grind)
    | (have r₁ := eq653
       have r₂ := eq895 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq653
       have r₂ := eq895 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq653 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq6815 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6814
  have eq6817 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6815
       grind)
    | exact superpose eq6815 eq16
    | exact resolve eq16 eq6815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6815
  have eq6818 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6817
       have r₂ := eq22 x
       grind)
    | exact resolve eq6817 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6817
  have eq6906 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq6818
       grind)
    | exact superpose eq6818 eq9
    | exact resolve eq9 eq6818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6907 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq6818
       grind)
    | exact superpose eq6818 eq9
    | exact resolve eq9 eq6818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6908 : y ≠ y ∨ x = y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6818
       grind)
    | exact superpose eq6818 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6818
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6818
       grind)
    | exact resolve eq13 eq6818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6818
  have eq6919 : x = y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6908
  have eq9884 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq6906 X0
       grind)
    | exact superpose eq6906 eq13
    | (have j0 := eq13 (σ x) (σ y)
       have j1 := eq6906 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6906 X0
       grind)
    | exact resolve eq13 eq6906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6906
  have eq9897 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have j0 := eq9884 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9884
  have eq9898 : ∀ X0 : G, (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have j0 := eq9897 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9897
  have eq9906 : ∀ X0 : G, (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq9898 X0
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq9898
    | (have j0 := eq9898 X0
       grind)
    | exact resolve eq9898 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9898
  have eq9908 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9906 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9906
    | (have j0 := eq9906 X0
       grind)
    | exact resolve eq9906 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9906
  have eq9922 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq6907 X0
       grind)
    | exact superpose eq6907 eq13
    | (have j0 := eq13 (σ x) (σ y)
       have j1 := eq6907 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6907 X0
       grind)
    | exact resolve eq13 eq6907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6907
  have eq9935 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | (have j0 := eq9922 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9922
  have eq9936 : ∀ X0 : G, (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | (have j0 := eq9935 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9935
  have eq9944 : ∀ X0 : G, (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | (have i₁ := eq9936 X0
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq9936
    | (have j0 := eq9936 X0
       grind)
    | exact resolve eq9936 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9936
  have eq9946 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9944 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9944
    | (have j0 := eq9944 X0
       grind)
    | exact resolve eq9944 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9944
  have eq18212 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4117 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4117
    | (have j0 := eq4117 (M.op (σ X0) (σ X0)) (k X0 X1)
       grind)
    | exact resolve eq4117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4117
  have eq18304 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18212 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18212
    | (have j0 := eq18212 X0 X1
       grind)
    | exact resolve eq18212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18212
  have eq18313 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18304 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq18304
    | (have j0 := eq18304 X0 X1
       grind)
    | exact resolve eq18304 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18304
  have eq18317 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18313 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq18313
    | (have j0 := eq18313 X0 X1
       grind)
    | exact resolve eq18313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18313
  have eq18419 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq18317 X1 X0
       grind)
    | exact superpose eq18317 eq10
    | (have j1 := eq18317 X1 X0
       grind)
    | exact resolve eq10 eq18317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18317
  have eq18483 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18419 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq18419
    | (have j0 := eq18419 X0 X1
       grind)
    | exact resolve eq18419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18419
  have eq18730 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq18483 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18483
  have eq18841 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18730 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq18730
    | (have j0 := eq18730 (σ (M.op X0 X0)) (k (σ X0) X1)
       grind)
    | exact resolve eq18730 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20734 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (σ X0))
       have i₂ := eq4447 X0 X1
       grind)
    | exact superpose eq4447 eq11
    | (have j1 := eq4447 X0 X1
       grind)
    | exact resolve eq11 eq4447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4447
  have eq20827 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20734 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq20734
    | (have j0 := eq20734 X0 X1
       grind)
    | exact resolve eq20734 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20734
  have eq20949 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4180 X0 X1
       have i₂ := eq20827 X0 X1
       grind)
    | exact superpose eq20827 eq4180
    | (have j0 := eq4180 X1 X0
       have j1 := eq20827 X1 X0
       grind)
    | (have r₁ := eq4180 X0 X1
       have r₂ := eq20827 X0 (k (σ X0) X1)
       grind)
    | exact resolve eq4180 eq20827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4180 eq20827
  have eq21013 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq20949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20949
  have eq21032 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq21013 X0 X1
       have j1 := eq18841 X1 X0
       grind)
    | (have r₁ := eq21013 X0 X0
       have r₂ := eq18841 X0 (M.op X0 (σ X0))
       grind)
    | (have r₁ := eq21013 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq18841 X0 X1
       grind)
    | (have r₁ := eq21013 X1 X0
       have r₂ := eq18841 X0 X1
       grind)
    | exact resolve eq21013 eq18841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18841 eq21013
  have eq25893 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6919
       grind)
    | exact superpose eq6919 eq16
    | exact resolve eq16 eq6919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6919
  have eq25894 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq25893
       have r₂ := eq22 x
       grind)
    | exact resolve eq25893 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25893
  have eq25897 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq653
       have i₂ := eq25894
       grind)
    | exact superpose eq25894 eq653
    | exact resolve eq653 eq25894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq25901 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq663 x y
       have i₂ := eq25894
       grind)
    | exact superpose eq25894 eq663
    | (have j0 := eq663 x y
       grind)
    | exact resolve eq663 eq25894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq25894
  have eq25925 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq25901
  have eq25928 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq25897
  have eq28595 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9908 (M.op x y)
       have i₂ := eq9946 x
       grind)
    | exact superpose eq9946 eq9908
    | exact resolve eq9908 eq9946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9908 eq9946
  have eq28633 : (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq28595
  have eq28638 : y = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq28633
       grind)
    | exact superpose eq28633 eq10
    | exact resolve eq10 eq28633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28633
  have eq28711 : x = y ∨ y = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq28638
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28638
    | exact resolve eq28638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28638
  have eq28713 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28711
       grind)
    | exact superpose eq28711 eq16
    | exact resolve eq16 eq28711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28711
  have eq28714 : (σ (k y x)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq28713
       have r₂ := eq22 x
       grind)
    | exact resolve eq28713 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28713
  have eq28950 : (k y x) = (τ (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq28714
       grind)
    | exact superpose eq28714 eq10
    | exact resolve eq10 eq28714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28714
  have eq29023 : (k y x) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28950
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq28950
    | exact resolve eq28950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28950
  have eq29030 : x = y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq29023
       grind)
    | exact superpose eq29023 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq29023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29023
  have eq30207 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29030
       grind)
    | exact superpose eq29030 eq16
    | exact resolve eq16 eq29030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29030
  have eq30219 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq30207
       have r₂ := eq22 x
       grind)
    | exact resolve eq30207 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30207
  have eq30225 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq30219
       grind)
    | exact superpose eq30219 eq9
    | exact resolve eq9 eq30219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31325 : y = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq30225 x
       have i₂ := eq30219
       grind)
    | exact superpose eq30219 eq30225
    | exact resolve eq30225 eq30219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30219
  have eq31385 : y = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq31325
  have eq31388 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq30225 y
       have i₂ := eq31385
       grind)
    | exact superpose eq31385 eq30225
    | exact resolve eq30225 eq31385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30225 eq31385
  have eq31437 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq31388
  have eq31441 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq25925
       have i₂ := eq31437
       grind)
    | exact superpose eq31437 eq25925
    | exact resolve eq25925 eq31437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25925
  have eq31517 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq31437
  have eq31518 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq31441
  have eq37331 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21032 (σ x) y
       have i₂ := eq31518
       grind)
    | exact superpose eq31518 eq21032
    | (have j0 := eq21032 (σ y) x
       grind)
    | (have r₁ := eq21032 (σ x) y
       have r₂ := eq31518
       grind)
    | exact resolve eq21032 eq31518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21032 eq31518
  have eq37367 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq37331
  have eq37368 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq37367
  have eq37386 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq37368
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq37368
    | exact resolve eq37368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37368
  have eq50381 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq37386
       grind)
    | exact superpose eq37386 eq10
    | exact resolve eq10 eq37386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37386
  have eq50470 : (σ (k y x)) = (σ (M.op y y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq50381
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq50381
    | exact resolve eq50381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50381
  have eq50493 : (k y x) = (τ (σ (M.op y y))) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq50470
       grind)
    | exact superpose eq50470 eq10
    | exact resolve eq10 eq50470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50470
  have eq50585 : (k y x) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq50493
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq50493
    | exact resolve eq50493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50493
  have eq50598 : (k y x) = (M.op y y) ∨ x = y := by
    first
    | (have j1 := eq18730 y x
       grind)
    | (have r₁ := eq50585
       have r₂ := eq18730 y x
       grind)
    | exact resolve eq50585 eq18730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18730 eq50585
  have eq50616 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq50598
       grind)
    | exact superpose eq50598 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq50598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50598
  have eq50667 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq50616
  have eq50670 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq50667
       have r₂ := eq31517
       grind)
    | exact resolve eq50667 eq31517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31517 eq50667
  have eq50673 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50670
       grind)
    | exact superpose eq50670 eq16
    | exact resolve eq16 eq50670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50670
  have eq50710 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq50673
       have r₂ := eq22 x
       grind)
    | exact resolve eq50673 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50673
  have eq50721 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25928
       have i₂ := eq50710
       grind)
    | exact superpose eq50710 eq25928
    | exact resolve eq25928 eq50710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25928
  have eq50861 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq50721
  have eq50901 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50861
       grind)
    | exact superpose eq50861 eq16
    | exact resolve eq16 eq50861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50914 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq50861
       grind)
    | exact superpose eq50861 eq9
    | exact resolve eq9 eq50861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50915 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ x)
       have i₂ := eq50861
       grind)
    | exact superpose eq50861 eq9
    | exact resolve eq9 eq50861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50861
  have eq59180 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50914 (M.op x (σ y))
       have i₂ := eq50915 x
       grind)
    | exact superpose eq50915 eq50914
    | exact resolve eq50914 eq50915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50914 eq50915
  have eq59228 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq59180
  have eq59243 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq59228
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq59228
    | exact resolve eq59228 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59228
  have eq59261 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq59243
       have i₂ := eq50710
       grind)
    | exact superpose eq50710 eq59243
    | exact resolve eq59243 eq50710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50710 eq59243
  have eq59274 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq59261
       have r₂ := eq50901
       grind)
    | exact resolve eq59261 eq50901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50901 eq59261
  have eq60001 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59274
       grind)
    | exact superpose eq59274 eq16
    | exact resolve eq16 eq59274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60016 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq59274
       grind)
    | exact superpose eq59274 eq10
    | exact resolve eq10 eq59274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59274
  have eq60114 : x = y := by
    first
    | (have i₁ := eq60016
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq60016
    | exact resolve eq60016 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60016
  have eq60116 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq60001
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq60001
    | exact resolve eq60001 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq60001
  have eq60123 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq60116
       have i₂ := eq60114
       grind)
    | exact superpose eq60114 eq60116
    | exact resolve eq60116 eq60114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60114 eq60116
  have eq60124 : False := by grind
  exact eq60124

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxy_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq21 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq24
  have eq43 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq57 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 (M.op X0 X1)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X1 X2
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op X2 X1) (M.op X0 X0)) (M.op X3 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60 X0 (M.op (M.op X1 X0) (M.op X2 X2)) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq60
    | exact resolve eq60 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X1
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X1
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 (M.op X1 X0)) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X1 (M.op X0 X1)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 (M.op X1 X0)) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq110
    | (have j0 := eq110 X0 X1
       grind)
    | exact resolve eq110 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq116 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0 X1
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq112
    | (have j0 := eq112 X0 X1
       grind)
    | exact resolve eq112 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq122 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (M.op X1 (σ X0)) X0
       have i₂ := eq114 (σ X0) X1
       grind)
    | exact superpose eq114 eq29
    | (have j1 := eq114 (σ X0) X1
       grind)
    | exact resolve eq29 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq125 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122
    | (have j0 := eq122 X0 X1
       grind)
    | exact resolve eq122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq401 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq59 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq59
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq401 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq418 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (M.op (τ X0) (τ X0))) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq411 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq411
    | (have j0 := eq411 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq411 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq419 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq411 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq411
    | (have j0 := eq411 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq411 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq420 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq411 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq411
    | (have j0 := eq411 (σ X0) (σ X1)
       grind)
    | exact resolve eq411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq411 (τ X0) X1
       grind)
    | exact superpose eq411 eq18
    | (have j1 := eq411 (τ X0) X1
       grind)
    | exact resolve eq18 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq443 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq419 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq444 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq446 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq443 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq443
    | exact resolve eq443 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq561 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 (τ X0) (τ (M.op X0 X0))
       have i₂ := eq446 X0
       grind)
    | exact superpose eq446 eq114
    | exact resolve eq114 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq446
  have eq563 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq561 X0
       have i₂ := eq31 (M.op X0 X0) X0
       grind)
    | exact superpose eq31 eq561
    | (have j0 := eq561 X0
       grind)
    | exact resolve eq561 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq565 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq563
  have eq624 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (σ (M.op (τ X0) (τ X0))) X0
       have i₂ := eq444 X0
       grind)
    | exact superpose eq444 eq57
    | exact resolve eq57 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq637 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq624 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq624
    | exact resolve eq624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq666 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) (σ (M.op X0 X0)) x
       have i₂ := eq637 X0
       grind)
    | exact superpose eq637 eq60
    | exact resolve eq60 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq1048 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq440 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq440
    | exact resolve eq440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1048 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1048
    | (have j0 := eq1048 X0 X1
       grind)
    | exact resolve eq1048 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq2413 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq440 X0 (τ X0)
       have i₂ := eq565 X0
       grind)
    | exact superpose eq565 eq440
    | (have j1 := eq565 X0
       grind)
    | exact resolve eq440 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq565
  have eq2455 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2413 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq2462 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2455 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2455
    | (have j0 := eq2455 X0
       grind)
    | exact resolve eq2455 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq2470 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2462 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2462
    | (have j0 := eq2462 X0
       grind)
    | exact resolve eq2462 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462
  have eq2493 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op X0 X0) X1
       have i₂ := eq2470 X0
       grind)
    | exact superpose eq2470 eq31
    | (have j1 := eq2470 X0
       grind)
    | exact resolve eq31 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470
  have eq2509 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2493 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq2493
    | (have j0 := eq2493 X0 X1
       grind)
    | exact resolve eq2493 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2493
  have eq2849 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    grind
  clear eq116
  have eq3056 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2849 X1 (M.op X0 X1)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq2849
    | exact resolve eq2849 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8891 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq420 y x
       grind)
    | exact superpose eq420 eq16
    | (have j1 := eq420 y x
       grind)
    | exact resolve eq16 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8938 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X1) (σ X0)
       have i₂ := eq420 X0 X1
       grind)
    | exact superpose eq420 eq57
    | (have j1 := eq420 (k X0 X1) X0
       grind)
    | exact resolve eq57 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8968 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq420 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9008 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8968 (M.op X0 X1) X1
       have i₂ := eq3056 X0 X1
       grind)
    | exact superpose eq3056 eq8968
    | (have j0 := eq8968 (M.op X0 X1) X1
       have j1 := eq3056 X0 X1
       grind)
    | exact resolve eq8968 eq3056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8968
  have eq9053 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9008 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9008
  have eq9256 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8891
       have i₂ := eq1102 y x
       grind)
    | exact superpose eq1102 eq8891
    | (have j1 := eq1102 (σ y) (σ x)
       grind)
    | (have r₁ := eq8891
       have r₂ := eq1102 y x
       grind)
    | exact resolve eq8891 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8891
  have eq9257 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9256
  have eq9261 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9257
       grind)
    | exact superpose eq9257 eq16
    | exact resolve eq16 eq9257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9282 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2849 (σ x) (σ y)
       have i₂ := eq9257
       grind)
    | exact superpose eq9257 eq2849
    | exact resolve eq2849 eq9257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2849
  have eq9284 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3056 (σ x) (σ y)
       have i₂ := eq9257
       grind)
    | exact superpose eq9257 eq3056
    | exact resolve eq3056 eq9257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3056
  have eq9300 : (σ x) = (σ (k y x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9284
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9284
    | exact resolve eq9284 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9284
  have eq9301 : (σ x) = (σ (k x y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9282
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq9282
    | exact resolve eq9282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9282
  have eq9306 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9300
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9300
    | exact resolve eq9300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9300
  have eq9307 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9301
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq9301
    | exact resolve eq9301 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9301
  have eq27724 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq2509
  have eq27910 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq27724 X0
       grind)
    | exact superpose eq27724 eq11
    | (have j1 := eq27724 X0
       grind)
    | exact resolve eq11 eq27724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27724
  have eq27981 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq27910 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq27910
    | (have j0 := eq27910 X0
       grind)
    | exact resolve eq27910 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27910
  have eq27982 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq27981 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27981
  have eq28904 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27982 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq27982
    | exact resolve eq27982 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29006 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28904 X0
       have i₂ := eq27982 X0
       grind)
    | exact superpose eq27982 eq28904
    | exact resolve eq28904 eq27982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27982 eq28904
  have eq29399 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (M.op (σ (M.op X1 X1)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq666 X1 (σ X0)
       have i₂ := eq29006 X0
       grind)
    | exact superpose eq29006 eq666
    | exact resolve eq666 eq29006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq58842 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq125 y (σ x)
       have i₂ := eq9257
       grind)
    | exact superpose eq9257 eq125
    | exact resolve eq125 eq9257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq9257
  have eq58972 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58842
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq58842
    | exact resolve eq58842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58842
  have eq59011 : (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58972
       have i₂ := eq29006 y
       grind)
    | exact superpose eq29006 eq58972
    | exact resolve eq58972 eq29006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58972
  have eq59781 : (M.op y y) = (τ (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq59011
       grind)
    | exact superpose eq59011 eq10
    | exact resolve eq10 eq59011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59011
  have eq59869 : y = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59781
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq59781
    | exact resolve eq59781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59781
  have eq59879 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq411 y x
       have i₂ := eq59869
       grind)
    | exact superpose eq59869 eq411
    | (have j0 := eq411 y x
       grind)
    | exact resolve eq411 eq59869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59869
  have eq59945 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq59879
  have eq60635 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59 y y
       have i₂ := eq59945
       grind)
    | exact superpose eq59945 eq59
    | exact resolve eq59 eq59945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59945
  have eq60715 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq60635
  have eq60728 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59 x y
       have i₂ := eq60715
       grind)
    | exact superpose eq60715 eq59
    | exact resolve eq59 eq60715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq60715
  have eq60836 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) y)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 y
       have i₂ := eq60728
       grind)
    | exact superpose eq60728 eq9
    | exact resolve eq9 eq60728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60841 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1 y
       have i₂ := eq60728
       grind)
    | exact superpose eq60728 eq60
    | exact resolve eq60 eq60728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq60842 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X1 X2) y) (M.op X0 X0))) = X2 ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 y X2 X1 X0
       have i₂ := eq60728
       grind)
    | exact superpose eq60728 eq68
    | exact resolve eq68 eq60728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq65449 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X1 y) (M.op (M.op X0 X1) y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq60836 (M.op X1 y) (M.op X0 X1)
       have i₂ := eq60841 X0 X1
       grind)
    | exact superpose eq60841 eq60836
    | exact resolve eq60836 eq60841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60836 eq60841
  have eq65454 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X1 y) (M.op (M.op X0 X1) y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq65449 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65449
  have eq120207 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ (M.op X0 X1)) (σ X1)
       have i₂ := eq9053 X0 X1
       grind)
    | exact superpose eq9053 eq57
    | (have j1 := eq9053 X0 X1
       grind)
    | exact resolve eq57 eq9053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123531 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq9306
       grind)
    | exact superpose eq9306 eq10
    | exact resolve eq10 eq9306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9306
  have eq123652 : (σ x) = (σ (k y x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq123531
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq123531
    | exact resolve eq123531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123531
  have eq123661 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1102 y x
       have i₂ := eq123652
       grind)
    | exact superpose eq123652 eq1102
    | (have j0 := eq1102 y x
       grind)
    | exact resolve eq1102 eq123652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123652
  have eq123768 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq123661
  have eq123885 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9261
       have i₂ := eq123768
       grind)
    | exact superpose eq123768 eq9261
    | (have r₁ := eq9261
       have r₂ := eq123768
       grind)
    | exact resolve eq9261 eq123768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9261 eq123768
  have eq123982 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq123885
  have eq123983 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq123982
  have eq124025 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1102 y x
       have i₂ := eq123983
       grind)
    | exact superpose eq123983 eq1102
    | (have j0 := eq1102 y x
       grind)
    | exact resolve eq1102 eq123983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq123983
  have eq124079 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq124025
  have eq124154 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29006 (M.op x y)
       have i₂ := eq124079
       grind)
    | exact superpose eq124079 eq29006
    | exact resolve eq29006 eq124079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124079
  have eq124196 : (σ (M.op y y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124154
       have i₂ := eq29006 y
       grind)
    | exact superpose eq29006 eq124154
    | exact resolve eq124154 eq29006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124154
  have eq130211 : (τ (σ (M.op y y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op (M.op x y) (M.op x y))
       have i₂ := eq124196
       grind)
    | exact superpose eq124196 eq10
    | exact resolve eq10 eq124196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124196
  have eq130338 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq130211
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq130211
    | exact resolve eq130211 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130211
  have eq159428 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq9307
       grind)
    | exact superpose eq9307 eq10
    | exact resolve eq10 eq9307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9307
  have eq159552 : (σ x) = (σ (k x y)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq159428
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq159428
    | exact resolve eq159428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159428
  have eq159572 : (τ (σ x)) = (k x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq159552
       grind)
    | exact superpose eq159552 eq10
    | exact resolve eq10 eq159552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159552
  have eq159696 : y = (k x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq159572
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq159572
    | exact resolve eq159572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159572
  have eq159699 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq159696
       have i₂ := eq411 x y
       grind)
    | exact superpose eq411 eq159696
    | (have j1 := eq411 x y
       grind)
    | exact resolve eq159696 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq159696
  have eq159752 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq159699
  have eq159838 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57 y x
       have i₂ := eq159752
       grind)
    | exact superpose eq159752 eq57
    | exact resolve eq57 eq159752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159752
  have eq160007 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq159838
  have eq160120 : ∀ X0 : G, x = (M.op x (M.op (M.op x y) (M.op X0 X0))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq60842 X0 y x
       have i₂ := eq160007
       grind)
    | exact superpose eq160007 eq60842
    | exact resolve eq60842 eq160007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60842
  have eq160137 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65454 y x
       have i₂ := eq160007
       grind)
    | exact superpose eq160007 eq65454
    | exact resolve eq65454 eq160007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65454 eq160007
  have eq160168 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq160137
  have eq160185 : ∀ X0 : G, x = (M.op x (M.op (M.op x y) (M.op X0 X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq160120 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160120
  have eq184172 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq130338
       have i₂ := eq160168
       grind)
    | exact superpose eq160168 eq130338
    | exact resolve eq130338 eq160168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160168
  have eq184747 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq184172
  have eq185260 : x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq160185 y
       have i₂ := eq184747
       grind)
    | exact superpose eq184747 eq160185
    | exact resolve eq160185 eq184747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160185 eq184747
  have eq185421 : x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq185260
  have eq207666 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq185421
       have i₂ := eq130338
       grind)
    | exact superpose eq130338 eq185421
    | exact resolve eq185421 eq130338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130338 eq185421
  have eq207878 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq207666
  have eq207883 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq207878
       have i₂ := eq60728
       grind)
    | exact superpose eq60728 eq207878
    | exact resolve eq207878 eq60728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60728 eq207878
  have eq208091 : x = (M.op x y) := by grind
  clear eq207883
  have eq208099 : y = (M.op y x) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq208091
       grind)
    | exact superpose eq208091 eq57
    | exact resolve eq57 eq208091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208141 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9053 x y
       have i₂ := eq208091
       grind)
    | exact superpose eq208091 eq9053
    | exact resolve eq9053 eq208091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9053
  have eq208347 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq120207 y x
       have i₂ := eq208099
       grind)
    | exact superpose eq208099 eq120207
    | exact resolve eq120207 eq208099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120207 eq208099
  have eq217767 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq208141
       grind)
    | exact superpose eq208141 eq16
    | exact resolve eq16 eq208141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208141
  have eq217934 : (σ x) ≠ (σ x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq217767
       have i₂ := eq208091
       grind)
    | exact superpose eq208091 eq217767
    | exact resolve eq217767 eq208091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217767
  have eq217935 : y = (k y x) := by grind
  clear eq217934
  have eq217969 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8938 y x
       have i₂ := eq217935
       grind)
    | exact superpose eq217935 eq8938
    | (have j0 := eq8938 y y
       grind)
    | exact resolve eq8938 eq217935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217993 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq217969
       have i₂ := eq29006 y
       grind)
    | exact superpose eq29006 eq217969
    | exact resolve eq217969 eq29006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217969
  have eq220294 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq208347
       grind)
    | exact superpose eq208347 eq16
    | exact resolve eq16 eq208347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208347
  have eq220462 : (σ x) ≠ (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq220294
       have i₂ := eq208091
       grind)
    | exact superpose eq208091 eq220294
    | exact resolve eq220294 eq208091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220294
  have eq220463 : x = (k x y) := by grind
  clear eq220462
  have eq220493 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8938 x y
       have i₂ := eq220463
       grind)
    | exact superpose eq220463 eq8938
    | (have j0 := eq8938 x x
       grind)
    | exact resolve eq8938 eq220463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8938 eq220463
  have eq220518 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq220493
       have i₂ := eq29006 x
       grind)
    | exact superpose eq29006 eq220493
    | exact resolve eq220493 eq29006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29006 eq220493
  have eq243530 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq217993
       grind)
    | exact superpose eq217993 eq16
    | exact resolve eq16 eq217993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217993
  have eq243707 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq243530
       have i₂ := eq208091
       grind)
    | exact superpose eq208091 eq243530
    | exact resolve eq243530 eq208091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243530
  have eq243708 : (σ y) = (σ (M.op y y)) := by grind
  clear eq243707
  have eq243762 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq29399 y X0
       have i₂ := eq243708
       grind)
    | exact superpose eq243708 eq29399
    | exact resolve eq29399 eq243708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29399 eq243708
  have eq635935 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq57 (σ y) (σ x)
       have i₂ := eq220518
       grind)
    | exact superpose eq220518 eq57
    | exact resolve eq57 eq220518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq220518
  have eq656030 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq635935
       grind)
    | exact superpose eq635935 eq16
    | exact resolve eq16 eq635935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635935
  have eq656314 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq656030
       have i₂ := eq208091
       grind)
    | exact superpose eq208091 eq656030
    | exact resolve eq656030 eq208091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656030
  have eq656315 : (σ x) = (σ (M.op x x)) := by grind
  clear eq656314
  have eq656445 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq243762 x
       have i₂ := eq656315
       grind)
    | exact superpose eq656315 eq243762
    | exact resolve eq243762 eq656315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243762 eq656315
  have eq691355 : (σ x) = (M.op (σ x) (σ (k y x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq656445
       have i₂ := eq420 y x
       grind)
    | exact superpose eq420 eq656445
    | (have j1 := eq420 (k y x) x
       grind)
    | exact resolve eq656445 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq656445
  have eq691644 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq691355
       have i₂ := eq217935
       grind)
    | exact superpose eq217935 eq691355
    | exact resolve eq691355 eq217935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217935 eq691355
  have eq691645 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq691644
  have eq691650 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq691645
       grind)
    | exact superpose eq691645 eq16
    | exact resolve eq16 eq691645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691645
  have eq691928 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq691650
       have i₂ := eq208091
       grind)
    | exact superpose eq208091 eq691650
    | exact resolve eq691650 eq208091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208091 eq691650
  have eq691929 : False := by grind
  exact eq691929

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_pxy_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
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
  clear eq35
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq59 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59
    | (have j0 := eq59 x y
       grind)
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ x) (σ y)
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq61 eq59
    | exact resolve eq59 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq62 eq59
    | exact resolve eq59 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq73 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq62 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : y ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq68 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op y (M.op x y)) = (k y (M.op x y)) := by
    first
    | exact superpose eq68 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y (M.op x y)
       have r₂ := eq68
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq99 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq71
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq100 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq99
  have eq102 : y = (M.op x y) ∨ (M.op y (M.op x y)) = (k y (M.op x y)) := by grind
  clear eq96
  have eq106 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62 eq100
    | exact resolve eq100 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq100
  have eq108 : y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61 eq102
    | exact resolve eq102 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq102
  have eq119 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq119
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq16
    | exact resolve eq16 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq131 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq130
    | exact resolve eq130 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq132 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq131
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq131
    | exact resolve eq131 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq133 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq132
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq132
    | exact resolve eq132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq742
    | exact resolve eq742 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq746 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq743
       have r₂ := eq27
       grind)
    | exact resolve eq743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq748 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq746
    | exact resolve eq746 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq750 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq748
    | exact resolve eq748 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq753 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq750 eq51
    | (have r₁ := eq51
       have r₂ := eq750
       grind)
    | exact resolve eq51 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq763 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq753
  have eq837 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq763 eq129
    | exact resolve eq129 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq763
  have eq845 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq837
    | exact resolve eq837 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq849 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq845
       have r₂ := eq50
       grind)
    | exact resolve eq845 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq852 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq119
    | exact resolve eq119 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq854 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq853
  have eq856 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq854
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq854
    | exact resolve eq854 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq857 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq856
  have eq858 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq852
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq852
    | exact resolve eq852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq861 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq857
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq857
    | exact resolve eq857 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq857
  have eq870 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq861 eq73
    | exact resolve eq73 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq873 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq861 eq106
    | exact resolve eq106 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq934 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq858 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq935 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq934
  have eq939 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq935
    | exact resolve eq935 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq940 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq939
  have eq945 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq940
    | exact resolve eq940 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq947 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq945 eq27
    | exact resolve eq27 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq945
  have eq1452 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq873 eq133
    | exact resolve eq133 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1456 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1452
  have eq1473 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1456 eq29
    | exact resolve eq29 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456
  have eq1562 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq1473
    | exact resolve eq1473 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1473
  have eq1612 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1562 eq29
    | exact resolve eq29 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1562
  have eq1686 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1612
    | exact resolve eq1612 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1612
  have eq1687 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1686
  have eq1688 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1687 eq20
    | exact resolve eq20 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1690 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1687 eq50
    | (have r₁ := eq50
       have r₂ := eq1687
       grind)
    | exact resolve eq50 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1687
  have eq1715 : x = (k y x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1690
  have eq1725 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1688
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1688
    | exact resolve eq1688 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1786 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1725 eq106
    | exact resolve eq106 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq1806 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1725 eq947
    | (have r₁ := eq947
       have r₂ := eq1725
       grind)
    | exact resolve eq947 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1825 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1806
  have eq1826 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1825
  have eq1845 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1786
       have r₂ := eq27
       grind)
    | exact resolve eq1786 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1852 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1826 eq27
    | exact resolve eq27 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2002 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq119
       have i₂ := eq1715
       grind)
    | exact superpose eq1715 eq119
    | exact resolve eq119 eq1715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq2008 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2002
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2002
    | exact resolve eq2002 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2179 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1826 eq1845
    | exact resolve eq1845 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826 eq1845
  have eq2190 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2179
  have eq2249 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1725 eq2008
    | exact resolve eq2008 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725 eq2008
  have eq2267 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2249
  have eq2628 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2267 eq2190
    | exact resolve eq2190 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190 eq2267
  have eq2632 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2628
  have eq2636 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2632
       have r₂ := eq1852
       grind)
    | exact resolve eq2632 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852 eq2632
  have eq2639 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2636 eq20
    | exact resolve eq20 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2649 : y = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2636 eq108
    | exact resolve eq108 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq2636
  have eq2663 : y = (k y x) ∨ x = y := by grind
  clear eq2649
  have eq2679 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2639
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2639
    | exact resolve eq2639 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639
  have eq2839 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq119
       have i₂ := eq2663
       grind)
    | exact superpose eq2663 eq119
    | exact resolve eq119 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq2663
  have eq2848 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2839
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2839
    | exact resolve eq2839 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839
  have eq2932 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2848 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2933 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2932
  have eq2940 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq2933
    | exact resolve eq2933 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2933
  have eq2943 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq2940
    | exact resolve eq2940 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2940
  have eq3003 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2943 eq51
    | (have r₁ := eq51
       have r₂ := eq2943
       grind)
    | exact resolve eq51 eq2943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3021 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2943
  have eq3029 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq3003
  have eq4096 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3029 eq2848
    | exact resolve eq2848 eq3029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848 eq3029
  have eq4099 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4096
  have eq4111 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq4099
       have r₂ := eq3021
       grind)
    | exact resolve eq4099 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021 eq4099
  have eq4185 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq4111 eq27
    | exact resolve eq27 eq4111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111
  have eq4214 : x = y := by
    first
    | (have r₁ := eq4185
       have r₂ := eq2679
       grind)
    | exact resolve eq4185 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2679 eq4185
  have eq4216 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4214
       grind)
    | exact superpose eq4214 eq24
    | exact resolve eq24 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq4258 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4216
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4216
    | exact resolve eq4216 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4216
  have eq4261 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4258 eq26
    | exact resolve eq26 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4274 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4258 eq133
    | exact resolve eq133 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq4292 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4258 eq870
    | (have r₁ := eq870
       have r₂ := eq4258
       grind)
    | exact resolve eq870 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq4295 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4258 eq956
    | (have r₁ := eq956
       have r₂ := eq4258
       grind)
    | exact resolve eq956 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956 eq4258
  have eq4324 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4295
  have eq4325 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4292
  have eq4333 : x = (M.op x y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4325
       have i₂ := eq4214
       grind)
    | exact superpose eq4214 eq4325
    | exact resolve eq4325 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4325
  have eq4334 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4333
  have eq4344 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4274
       have i₂ := eq4214
       grind)
    | exact superpose eq4214 eq4274
    | exact resolve eq4274 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274
  have eq4345 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4344
  have eq4671 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4324 eq27
    | exact resolve eq27 eq4324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4324
  have eq5183 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4345 eq4334
    | exact resolve eq4334 eq4345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334 eq4345
  have eq5193 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq5183
  have eq5200 : x = (M.op x y) := by
    first
    | (have r₁ := eq5193
       have r₂ := eq4671
       grind)
    | exact resolve eq5193 eq4671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671 eq5193
  have eq5208 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq5200 eq20
    | exact resolve eq20 eq5200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq5216 : x ≠ y ∨ x = (k y x) := by
    first
    | exact superpose eq5200 eq83
    | exact resolve eq83 eq5200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq5200
  have eq5265 : x = (k y x) := by
    first
    | (have r₁ := eq5216
       have r₂ := eq4214
       grind)
    | exact resolve eq5216 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq5273 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5208
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5208
    | exact resolve eq5208 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5208
  have eq5277 : x = (k x x) := by
    first
    | (have i₁ := eq5265
       have i₂ := eq4214
       grind)
    | exact superpose eq4214 eq5265
    | exact resolve eq5265 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214 eq5265
  have eq5313 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5273 eq4261
    | exact resolve eq4261 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4261
  have eq5346 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq5277
       grind)
    | exact superpose eq5277 eq43
    | exact resolve eq43 eq5277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq5277
  have eq5357 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5273 eq5346
    | exact resolve eq5346 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5346
  have eq5362 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5357
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5357
    | exact resolve eq5357 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5357
  have eq5365 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5273 eq5362
    | exact resolve eq5362 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273 eq5362
  have eq5950 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5365 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq5365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5365
  have eq5951 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5950
  have eq5953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5313 eq5951
    | exact resolve eq5951 eq5313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5313 eq5951
  have eq5958 : False := by grind
  exact eq5958

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_y_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  clear eq17
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 (M.op X1 X0)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X2
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) X0
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X1
       have r₂ := eq24 X0 X1
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq35 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq33
    | exact resolve eq33 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X0)
       have r₂ := eq26 X0 X1
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq48 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq47
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq101 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq107 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 (σ X1)) X1
       have i₂ := eq35 (σ X1) X0
       grind)
    | exact superpose eq35 eq22
    | exact resolve eq22 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq147 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (M.op X1 (σ X0))
       have i₂ := eq48 X1 (σ X0)
       grind)
    | exact superpose eq48 eq78
    | exact resolve eq78 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq160 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq147
    | exact resolve eq147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq182 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq63 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X1)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq24
    | (have j1 := eq63 X1 X0
       grind)
    | exact resolve eq24 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq216 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq182 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq182 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq182 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq182 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq221 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq216
    | (have j0 := eq216 X0 X1
       grind)
    | exact resolve eq216 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq701 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq202
    | exact resolve eq202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq202 y x
       grind)
    | exact superpose eq202 eq16
    | (have j1 := eq202 y x
       grind)
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 : G, (k X0 (τ (σ (k X0 X1)))) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 (σ X1)
       have i₂ := eq202 X0 X1
       grind)
    | exact superpose eq202 eq160
    | (have j1 := eq202 X0 X1
       grind)
    | exact resolve eq160 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq202 X0 X1
       grind)
    | exact superpose eq202 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq202 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq202 X0 X1
       grind)
    | exact resolve eq12 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq722 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq722 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq722 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq740 : ∀ X0 X1 : G, (k X0 (k X0 X1)) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq710
    | (have j0 := eq710 X0 X1
       grind)
    | exact resolve eq710 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq743 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq701
    | (have j0 := eq701 X0 X1
       grind)
    | exact resolve eq701 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq701
  have eq744 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq738 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq738
    | (have j0 := eq738 X0 X1
       grind)
    | exact resolve eq738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq1690 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq221 (M.op X1 X0) X0
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq221
    | (have j0 := eq221 (M.op X0 X1) X1
       grind)
    | exact resolve eq221 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq1717 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1690 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq2002 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq735 (τ X1) (τ X0)
       have i₂ := eq101 X1 X0
       grind)
    | exact superpose eq101 eq735
    | (have j0 := eq735 (τ X1) (τ X0)
       grind)
    | exact resolve eq735 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq735
  have eq2019 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2002 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2002
    | (have j0 := eq2002 X0 X1
       grind)
    | exact resolve eq2002 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2030 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2019 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2019
    | (have j0 := eq2019 X0 X1
       grind)
    | exact resolve eq2019 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2039 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2030 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2030
    | (have j0 := eq2030 X0 X1
       grind)
    | exact resolve eq2030 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030
  have eq2044 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2039 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2039
    | (have j0 := eq2039 X0 X1
       grind)
    | exact resolve eq2039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq2448 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq743 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq743
    | exact resolve eq743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq5457 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq707
       have i₂ := eq2448 y x
       grind)
    | exact superpose eq2448 eq707
    | (have j1 := eq2448 (σ y) (σ x)
       grind)
    | exact resolve eq707 eq2448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq5460 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5457
  have eq5464 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107 (σ x) y
       have i₂ := eq5460
       grind)
    | exact superpose eq5460 eq107
    | exact resolve eq107 eq5460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq5465 : y = (k y (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq160 y (σ x)
       have i₂ := eq5460
       grind)
    | exact superpose eq5460 eq160
    | exact resolve eq160 eq5460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq5460
  have eq5500 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5465
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5465
    | exact resolve eq5465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465
  have eq5501 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5464
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5464
    | exact resolve eq5464 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5464
  have eq5610 : x ≠ y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2044 y x
       have i₂ := eq5500
       grind)
    | exact superpose eq5500 eq2044
    | (have j0 := eq2044 y x
       grind)
    | exact resolve eq2044 eq5500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5612 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2448 y x
       have i₂ := eq5500
       grind)
    | exact superpose eq5500 eq2448
    | (have j0 := eq2448 y x
       grind)
    | exact resolve eq2448 eq5500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5500
  have eq5619 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5612
  have eq5620 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq5610
  have eq5969 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2448 x y
       have i₂ := eq5501
       grind)
    | exact superpose eq5501 eq2448
    | (have j0 := eq2448 x y
       grind)
    | exact resolve eq2448 eq5501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448 eq5501
  have eq6118 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26 y x
       have i₂ := eq5619
       grind)
    | exact superpose eq5619 eq26
    | exact resolve eq26 eq5619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6269 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) y)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 y
       have i₂ := eq6118
       grind)
    | exact superpose eq6118 eq9
    | exact resolve eq9 eq6118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6118
  have eq15173 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq5969
       grind)
    | exact superpose eq5969 eq24
    | exact resolve eq24 eq5969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5969
  have eq15217 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq15173
  have eq15552 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26 x y
       have i₂ := eq15217
       grind)
    | exact superpose eq15217 eq26
    | exact resolve eq26 eq15217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq15589 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6269 x y
       have i₂ := eq15217
       grind)
    | exact superpose eq15217 eq6269
    | exact resolve eq6269 eq15217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6269 eq15217
  have eq15592 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq15589
  have eq15808 : x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35 y x
       have i₂ := eq15552
       grind)
    | exact superpose eq15552 eq35
    | exact resolve eq35 eq15552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq15552
  have eq16922 : x = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq740 x y
       have i₂ := eq15808
       grind)
    | exact superpose eq15808 eq740
    | (have j0 := eq740 x y
       grind)
    | exact resolve eq740 eq15808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15808
  have eq16941 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq2044 (σ x) (σ y)
       grind)
    | (have r₁ := eq16922
       have r₂ := eq2044 x x
       grind)
    | exact resolve eq16922 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044 eq16922
  have eq17604 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15592
       have i₂ := eq5619
       grind)
    | exact superpose eq5619 eq15592
    | exact resolve eq15592 eq5619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5619 eq15592
  have eq17658 : x = (M.op x y) ∨ x = y := by grind
  clear eq17604
  have eq17660 : x = (M.op x y) := by
    first
    | (have r₁ := eq17658
       have r₂ := eq5620
       grind)
    | exact resolve eq17658 eq5620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5620 eq17658
  have eq17805 : y = (k y x) := by
    first
    | (have i₁ := eq48 x y
       have i₂ := eq17660
       grind)
    | exact superpose eq17660 eq48
    | exact resolve eq48 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq18541 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq740 y x
       have i₂ := eq17805
       grind)
    | exact superpose eq17805 eq740
    | (have j0 := eq740 y x
       grind)
    | exact resolve eq740 eq17805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq21481 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24 (σ y) (σ x)
       have i₂ := eq16941
       grind)
    | exact superpose eq16941 eq24
    | exact resolve eq24 eq16941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16941
  have eq24181 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21481
       grind)
    | exact superpose eq21481 eq16
    | exact resolve eq16 eq21481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21481
  have eq24250 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24181
       have i₂ := eq17660
       grind)
    | exact superpose eq17660 eq24181
    | exact resolve eq24181 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24181
  have eq24251 : x = (M.op x x) := by grind
  clear eq24250
  have eq24690 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1717 x x
       have i₂ := eq24251
       grind)
    | exact superpose eq24251 eq1717
    | exact resolve eq1717 eq24251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717 eq24251
  have eq24696 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq24690
  have eq25667 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq27 (σ x) (σ x) x
       have i₂ := eq24696
       grind)
    | exact superpose eq24696 eq27
    | exact resolve eq27 eq24696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq24696
  have eq163242 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18541
       grind)
    | exact superpose eq18541 eq16
    | exact resolve eq16 eq18541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18541
  have eq163415 : (σ x) ≠ (σ x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq163242
       have i₂ := eq17660
       grind)
    | exact superpose eq17660 eq163242
    | exact resolve eq163242 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163242
  have eq163416 : y = (k y y) := by grind
  clear eq163415
  have eq164281 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq744 y y
       have i₂ := eq163416
       grind)
    | exact superpose eq163416 eq744
    | exact resolve eq744 eq163416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq163416
  have eq164362 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq164281
  have eq168105 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq25667 (σ y)
       have i₂ := eq164362
       grind)
    | exact superpose eq164362 eq25667
    | exact resolve eq25667 eq164362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25667 eq164362
  have eq300458 : (σ x) = (M.op (σ x) (σ (k y x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq168105
       have i₂ := eq202 y x
       grind)
    | exact superpose eq202 eq168105
    | (have j1 := eq202 (k y x) x
       grind)
    | exact resolve eq168105 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq168105
  have eq300656 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq300458
       have i₂ := eq17805
       grind)
    | exact superpose eq17805 eq300458
    | exact resolve eq300458 eq17805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17805 eq300458
  have eq300657 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq300656
  have eq301634 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq300657
       grind)
    | exact superpose eq300657 eq16
    | exact resolve eq16 eq300657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300657
  have eq301858 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq301634
       have i₂ := eq17660
       grind)
    | exact superpose eq17660 eq301634
    | exact resolve eq301634 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17660 eq301634
  have eq301859 : False := by grind
  exact eq301859

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyy_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 (M.op X1 X0)
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X2
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) X0
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X1
       have r₂ := eq21 X0 X1
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X0)
       have r₂ := eq26 X0 X1
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq58 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq72 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op X0 (σ X1)) X1
       have i₂ := eq30 (σ X1) X0
       grind)
    | exact superpose eq30 eq58
    | exact resolve eq58 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq140 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 (M.op X1 (σ X0))
       have i₂ := eq44 X1 (σ X0)
       grind)
    | exact superpose eq44 eq72
    | exact resolve eq72 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq72
  have eq152 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq140
    | exact resolve eq140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq186 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) (σ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq21
    | (have j1 := eq47 X1 X0
       grind)
    | exact resolve eq21 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X0) (σ X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq30
    | (have j1 := eq47 X1 X0
       grind)
    | exact resolve eq30 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq194 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq205 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq189 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq189 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq212 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq205
    | (have j0 := eq205 X0 X1
       grind)
    | exact resolve eq205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq688 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq194
    | exact resolve eq194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq194 y x
       grind)
    | exact superpose eq194 eq16
    | (have j1 := eq194 y x
       grind)
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 : G, (k X0 (τ (σ (k X0 X1)))) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 (σ X1)
       have i₂ := eq194 X0 X1
       grind)
    | exact superpose eq194 eq152
    | (have j1 := eq194 X0 X1
       grind)
    | exact resolve eq152 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1) (σ X0)
       have i₂ := eq194 X0 X1
       grind)
    | exact superpose eq194 eq21
    | (have j1 := eq194 (k X0 X1) X0
       grind)
    | exact resolve eq21 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq194 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 X1 : G, (k X0 (k X0 X1)) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq697
    | (have j0 := eq697 X0 X1
       grind)
    | exact resolve eq697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq729 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq688
    | (have j0 := eq688 X0 X1
       grind)
    | exact resolve eq688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq688
  have eq1922 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq722 (τ X1) (τ X0)
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq722
    | (have j0 := eq722 (τ X1) (τ X0)
       grind)
    | exact resolve eq722 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1939 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1922 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1922
    | (have j0 := eq1922 X0 X1
       grind)
    | exact resolve eq1922 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922
  have eq1950 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1939 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1939
    | (have j0 := eq1939 X0 X1
       grind)
    | exact resolve eq1939 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq1959 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1950 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1950
    | (have j0 := eq1950 X0 X1
       grind)
    | exact resolve eq1950 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950
  have eq1964 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1959 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1959
    | (have j0 := eq1959 X0 X1
       grind)
    | exact resolve eq1959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq2417 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq729 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq729
    | exact resolve eq729 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq4912 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq212 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq212
    | exact resolve eq212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq5007 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4912 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq4912
    | (have j0 := eq4912 X0 X1
       grind)
    | exact resolve eq4912 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4912
  have eq5011 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5007 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq5007
    | (have j0 := eq5007 X0 X1
       grind)
    | exact resolve eq5007 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq5007
  have eq5236 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq694
       have i₂ := eq2417 y x
       grind)
    | exact superpose eq2417 eq694
    | (have j1 := eq2417 (σ y) (σ x)
       grind)
    | exact resolve eq694 eq2417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq5239 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5236
  have eq5300 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq712 (τ X0) (τ X1)
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq712
    | (have j0 := eq712 (τ (k X0 X1)) (τ X0)
       grind)
    | exact resolve eq712 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq712
  have eq5368 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5300 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5300
    | (have j0 := eq5300 X0 X1
       grind)
    | exact resolve eq5300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5300
  have eq5381 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5368 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5368
    | (have j0 := eq5368 X0 X1
       grind)
    | exact resolve eq5368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5368
  have eq5386 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5381 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5381
    | (have j0 := eq5381 X0 X1
       grind)
    | exact resolve eq5381 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5381
  have eq5391 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5386 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5386
    | (have j0 := eq5386 X0 X1
       grind)
    | exact resolve eq5386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5386
  have eq5811 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101 (σ x) y
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq101
    | exact resolve eq101 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq5812 : y = (k y (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq152 y (σ x)
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq152
    | exact resolve eq152 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq5239
  have eq5846 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5812
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5812
    | exact resolve eq5812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5812
  have eq5847 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5811
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5811
    | exact resolve eq5811 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5811
  have eq5851 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq5846
       have r₂ := eq12 y x
       grind)
    | exact resolve eq5846 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5846
  have eq5904 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq726 y x
       have i₂ := eq5851
       grind)
    | exact superpose eq5851 eq726
    | (have j0 := eq726 y x
       grind)
    | exact resolve eq726 eq5851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5907 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1964 y x
       have i₂ := eq5851
       grind)
    | exact superpose eq5851 eq1964
    | (have j0 := eq1964 y x
       grind)
    | exact resolve eq1964 eq5851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq5908 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2417 y x
       have i₂ := eq5851
       grind)
    | exact superpose eq5851 eq2417
    | (have j0 := eq2417 y x
       grind)
    | exact resolve eq2417 eq5851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5912 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5391 y x
       have i₂ := eq5851
       grind)
    | exact superpose eq5851 eq5391
    | (have j0 := eq5391 y y
       grind)
    | exact resolve eq5391 eq5851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5391 eq5851
  have eq6549 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2417 x y
       have i₂ := eq5847
       grind)
    | exact superpose eq5847 eq2417
    | (have j0 := eq2417 x y
       grind)
    | exact resolve eq2417 eq5847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417 eq5847
  have eq7177 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) y)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 y
       have i₂ := eq5912
       grind)
    | exact superpose eq5912 eq9
    | exact resolve eq9 eq5912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5912
  have eq8935 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5904
       grind)
    | exact superpose eq5904 eq16
    | exact resolve eq16 eq5904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5904
  have eq16778 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5011 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5011
    | exact resolve eq5011 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5011
  have eq17389 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq16778 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16778
  have eq23645 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21 y x
       have i₂ := eq6549
       grind)
    | exact superpose eq6549 eq21
    | exact resolve eq21 eq6549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6549
  have eq23698 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq23645
  have eq23931 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26 x y
       have i₂ := eq23698
       grind)
    | exact superpose eq23698 eq26
    | exact resolve eq26 eq23698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq23975 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7177 x y
       have i₂ := eq23698
       grind)
    | exact superpose eq23698 eq7177
    | exact resolve eq7177 eq23698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7177 eq23698
  have eq23980 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq23975
  have eq24093 : x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq30 y x
       have i₂ := eq23931
       grind)
    | exact superpose eq23931 eq30
    | exact resolve eq30 eq23931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23931
  have eq25115 : x = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq726 x y
       have i₂ := eq24093
       grind)
    | exact superpose eq24093 eq726
    | (have j0 := eq726 x y
       grind)
    | exact resolve eq726 eq24093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq24093
  have eq25134 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have j1 := eq17389 x x
       grind)
    | (have r₁ := eq25115
       have r₂ := eq17389 x x
       grind)
    | exact resolve eq25115 eq17389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17389 eq25115
  have eq27044 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23980
       have i₂ := eq5908
       grind)
    | exact superpose eq5908 eq23980
    | exact resolve eq23980 eq5908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5908 eq23980
  have eq27107 : x = (M.op x y) ∨ x = y := by grind
  clear eq27044
  have eq27108 : x = (M.op x y) := by
    first
    | (have r₁ := eq27107
       have r₂ := eq5907
       grind)
    | exact resolve eq27107 eq5907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5907 eq27107
  have eq27497 : (σ x) ≠ (σ x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq8935
       have i₂ := eq27108
       grind)
    | exact superpose eq27108 eq8935
    | exact resolve eq8935 eq27108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8935
  have eq27508 : x = (k x y) := by
    first
    | (have i₁ := eq30 y x
       have i₂ := eq27108
       grind)
    | exact superpose eq27108 eq30
    | exact resolve eq30 eq27108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq27558 : y = (k y y) := by grind
  clear eq27497
  have eq28666 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq722 y y
       have i₂ := eq27558
       grind)
    | exact superpose eq27558 eq722
    | (have j0 := eq722 y y
       grind)
    | exact resolve eq722 eq27558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27558
  have eq28695 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq28666
  have eq30344 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq27 (σ y) (σ y) x
       have i₂ := eq28695
       grind)
    | exact superpose eq28695 eq27
    | exact resolve eq27 eq28695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28695
  have eq182867 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq21 (σ y) (σ x)
       have i₂ := eq25134
       grind)
    | exact superpose eq25134 eq21
    | exact resolve eq21 eq25134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25134
  have eq202571 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq182867
       grind)
    | exact superpose eq182867 eq16
    | exact resolve eq16 eq182867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182867
  have eq202755 : (σ x) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq202571
       have i₂ := eq27108
       grind)
    | exact superpose eq27108 eq202571
    | exact resolve eq202571 eq27108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202571
  have eq202756 : x = (k x x) := by grind
  clear eq202755
  have eq203414 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq722 x x
       have i₂ := eq202756
       grind)
    | exact superpose eq202756 eq722
    | (have j0 := eq722 x x
       grind)
    | exact resolve eq722 eq202756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq202756
  have eq203513 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq203414
  have eq206876 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq30344 (σ x)
       have i₂ := eq203513
       grind)
    | exact superpose eq203513 eq30344
    | exact resolve eq30344 eq203513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30344 eq203513
  have eq372936 : (σ y) = (M.op (σ y) (σ (k x y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq206876
       have i₂ := eq194 x y
       grind)
    | exact superpose eq194 eq206876
    | (have j1 := eq194 (k x y) y
       grind)
    | exact resolve eq206876 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq206876
  have eq373162 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq372936
       have i₂ := eq27508
       grind)
    | exact superpose eq27508 eq372936
    | exact resolve eq372936 eq27508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27508 eq372936
  have eq373163 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq373162
  have eq374448 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21 (σ y) (σ x)
       have i₂ := eq373163
       grind)
    | exact superpose eq373163 eq21
    | exact resolve eq21 eq373163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq373163
  have eq376023 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq374448
       grind)
    | exact superpose eq374448 eq16
    | exact resolve eq16 eq374448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374448
  have eq376274 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq376023
       have i₂ := eq27108
       grind)
    | exact superpose eq27108 eq376023
    | exact resolve eq376023 eq27108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27108 eq376023
  have eq376275 : False := by grind
  exact eq376275

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pyx_pxy_pxx_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq22
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1002 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq1003 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1003
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq1003
    | exact resolve eq1003 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1044 : (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1002
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq1002
    | exact resolve eq1002 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1078 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq19157 : (M.op x y) ≠ (k y y) ∨ (M.op x y) = (M.op y x) ∨ (k y x) = (k y y) := by
    first
    | (have i₁ := eq1078 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1078
    | (have j0 := eq1078 y x
       grind)
    | exact resolve eq1078 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19158 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq1078
    | (have j0 := eq1078 (σ y) (σ x)
       grind)
    | exact resolve eq1078 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq19807 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq19157
       have i₂ := eq1044
       grind)
    | exact superpose eq1044 eq19157
    | (have r₁ := eq19157
       have r₂ := eq1044
       grind)
    | exact resolve eq19157 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq19157
  have eq19808 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq19807
  have eq19809 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq19808
  have eq19815 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq19809
       grind)
    | exact superpose eq19809 eq39
    | exact resolve eq39 eq19809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19809
  have eq19817 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq19815
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19815
    | exact resolve eq19815 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19815
  have eq19821 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq19817
    | exact resolve eq19817 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19817
  have eq19957 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1043 eq19158
    | (have r₁ := eq19158
       have r₂ := eq1043
       grind)
    | exact resolve eq19158 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043 eq19158
  have eq19958 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq19957
  have eq19959 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq19958
  have eq19966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq19959 eq19821
    | exact resolve eq19821 eq19959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19971 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19966
       have r₂ := eq27
       grind)
    | exact resolve eq19966 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19966
  have eq19979 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19971 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19971
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19971
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19971
       grind)
    | exact resolve eq13 eq19971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19971
  have eq19980 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19979
       have r₂ := eq26
       grind)
    | exact resolve eq19979 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19979
  have eq19983 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19821 eq19980
    | exact resolve eq19980 eq19821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19821 eq19980
  have eq19986 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19983
       have r₂ := eq27
       grind)
    | exact resolve eq19983 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19983
  have eq19994 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19986
       grind)
    | exact superpose eq19986 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq19986
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19986
       grind)
    | exact resolve eq13 eq19986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19986
  have eq19995 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq19994
       have r₂ := eq18
       grind)
    | exact resolve eq19994 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19994
  have eq20004 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq19995
       grind)
    | exact superpose eq19995 eq39
    | exact resolve eq39 eq19995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq19995
  have eq20005 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq20004
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20004
    | exact resolve eq20004 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq20004
  have eq20009 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq20005
    | exact resolve eq20005 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq20005
  have eq20031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq20009 eq19959
    | exact resolve eq19959 eq20009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19959
  have eq20036 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq20031
       have r₂ := eq27
       grind)
    | exact resolve eq20031 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20031
  have eq20065 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20036 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20036
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20036
       grind)
    | exact resolve eq13 eq20036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20036
  have eq20066 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq20065
       have r₂ := eq26
       grind)
    | exact resolve eq20065 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq20065
  have eq20069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20009 eq20066
    | exact resolve eq20066 eq20009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20009 eq20066
  have eq20072 : False := by grind
  exact eq20072

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pxy_pyx_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq748 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq3158 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq748 x y
       grind)
    | exact superpose eq748 eq16
    | (have j1 := eq748 x y
       grind)
    | exact resolve eq16 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3162 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq748 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3163 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq748 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19706 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3163 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq3163
    | (have j0 := eq3163 (τ X0) (τ X1)
       grind)
    | exact resolve eq3163 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3163
  have eq19893 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19706 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq19706
    | (have j0 := eq19706 X0 X1
       grind)
    | exact resolve eq19706 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19706
  have eq19984 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19893 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19893
    | (have j0 := eq19893 X0 X1
       grind)
    | exact resolve eq19893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19893
  have eq20068 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19984 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19984
    | (have j0 := eq19984 X0 X1
       grind)
    | exact resolve eq19984 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19984
  have eq20111 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20068 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20068
    | (have j0 := eq20068 X0 X1
       grind)
    | exact resolve eq20068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20068
  have eq20129 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20111 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20111
    | (have j0 := eq20111 X0 X1
       grind)
    | exact resolve eq20111 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20111
  have eq20141 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20129 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20129
    | (have j0 := eq20129 X0 X1
       grind)
    | exact resolve eq20129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20129
  have eq26665 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3158
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq3158
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq3158 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26666 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq26665
  have eq30699 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) ≠ (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3162 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3162
    | exact resolve eq3162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30720 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3162 X1 X0
       have i₂ := eq748 X0 X1
       grind)
    | exact superpose eq748 eq3162
    | (have j0 := eq3162 X0 X1
       have j1 := eq748 X0 X1
       grind)
    | (have r₁ := eq3162 X0 X0
       have r₂ := eq748 X0 X0
       grind)
    | exact resolve eq3162 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq30725 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30720 X0 X1
       have j1 := eq3162 X0 X1
       grind)
    | (have r₁ := eq30720 X0 X1
       have r₂ := eq3162 X0 X1
       grind)
    | exact resolve eq30720 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162 eq30720
  have eq30726 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30699 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq30699
    | (have j0 := eq30699 X0 X1
       grind)
    | exact resolve eq30699 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq30699
  have eq41717 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30726 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30726
    | exact resolve eq30726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30726
  have eq242944 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq26666
       grind)
    | exact superpose eq26666 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq26666
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26666
       grind)
    | exact resolve eq12 eq26666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26666
  have eq242945 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq242944
  have eq1904862 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30725 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq30725
    | (have j0 := eq30725 (τ X1) (τ X0)
       grind)
    | exact resolve eq30725 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq30725
  have eq1905358 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1904862 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq1904862
    | (have j0 := eq1904862 X0 X1
       grind)
    | exact resolve eq1904862 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1904862
  have eq1905842 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1905358 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1905358
    | (have j0 := eq1905358 X0 X1
       grind)
    | exact resolve eq1905358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905358
  have eq1906296 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1905842 X1 X0
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq1905842
    | (have j0 := eq1905842 X0 X1
       grind)
    | (have r₁ := eq1905842 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq1905842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905842
  have eq1906726 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1906296 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1906296
    | (have j0 := eq1906296 X0 X1
       grind)
    | exact resolve eq1906296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906296
  have eq1907131 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1906726 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1906726
    | (have j0 := eq1906726 X0 X1
       grind)
    | exact resolve eq1906726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906726
  have eq1907526 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1907131 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1907131
    | (have j0 := eq1907131 X0 X1
       grind)
    | exact resolve eq1907131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907131
  have eq1907906 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1907526 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1907526
    | (have j0 := eq1907526 X0 X1
       grind)
    | exact resolve eq1907526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907526
  have eq1908150 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1907906 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1907906
    | (have j0 := eq1907906 X0 X1
       grind)
    | exact resolve eq1907906 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907906
  have eq1908258 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1908150 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1908150
    | (have j0 := eq1908150 X0 X1
       grind)
    | exact resolve eq1908150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908150
  have eq3380100 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq242945
       grind)
    | exact superpose eq242945 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq242945
       grind)
    | exact resolve eq12 eq242945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3380101 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq242945
       grind)
    | exact superpose eq242945 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq242945
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq242945
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq242945
       grind)
    | exact resolve eq13 eq242945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242945
  have eq3380104 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq3380101
  have eq3380106 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq3380100
       have r₂ := eq3380104
       grind)
    | exact resolve eq3380100 eq3380104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3380100 eq3380104
  have eq3383448 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3380106
       grind)
    | exact superpose eq3380106 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3380106
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3380106
       grind)
    | exact resolve eq13 eq3380106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3380106
  have eq3383449 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq3383448
  have eq3383450 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq3383449
  have eq3383452 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq3383450
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq3383450 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383450
  have eq3383456 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq3383452
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3383452
    | exact resolve eq3383452 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383452
  have eq3383462 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3383456
       grind)
    | exact superpose eq3383456 eq16
    | exact resolve eq16 eq3383456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383456
  have eq3383531 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3383462
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq3383462
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq3383462 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383462
  have eq3383534 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq3383531
  have eq3383535 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq3383534
  have eq3383537 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3383535
       grind)
    | exact superpose eq3383535 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq3383535
       grind)
    | exact resolve eq12 eq3383535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3383538 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3383535
       grind)
    | exact superpose eq3383535 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3383535
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3383535
       grind)
    | exact resolve eq13 eq3383535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3383539 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq3383535
       grind)
    | exact superpose eq3383535 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3383535
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3383535
       grind)
    | exact resolve eq13 eq3383535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383535
  have eq3383540 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq3383539
  have eq3383541 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq3383540
  have eq3383542 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq3383538
  have eq3383543 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq3383542
  have eq3383544 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq3383537
  have eq3383545 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq3383541
       have r₂ := eq12 x y
       grind)
    | exact resolve eq3383541 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383541
  have eq3383546 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq3383544
       have r₂ := eq3383543
       grind)
    | exact resolve eq3383544 eq3383543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383543 eq3383544
  have eq3383548 : x ≠ x ∨ x = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq3383546
       grind)
    | exact superpose eq3383546 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq3383546
       grind)
    | exact resolve eq12 eq3383546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383546
  have eq3383549 : (M.op x y) = (k y x) ∨ x = (k x y) := by grind
  clear eq3383548
  have eq3383669 : (M.op x y) ≠ (k x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1908258 x y
       have i₂ := eq3383549
       grind)
    | exact superpose eq3383549 eq1908258
    | (have j0 := eq1908258 x y
       grind)
    | exact resolve eq1908258 eq3383549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908258 eq3383549
  have eq3383676 : (M.op x y) ≠ (k x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq20141 x y
       grind)
    | (have r₁ := eq3383669
       have r₂ := eq20141 x y
       grind)
    | exact resolve eq3383669 eq20141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20141 eq3383669
  have eq3383679 : y = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq3383676
       have r₂ := eq14 x y
       grind)
    | exact resolve eq3383676 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383676
  have eq3383709 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq41717 x y
       have i₂ := eq3383545
       grind)
    | exact superpose eq3383545 eq41717
    | (have j0 := eq41717 x y
       grind)
    | (have r₁ := eq41717 x y
       have r₂ := eq3383545
       grind)
    | exact resolve eq41717 eq3383545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41717
  have eq3383799 : y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) := by grind
  clear eq3383709
  have eq3383829 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq3383679
  have eq3387226 : y ≠ y ∨ y = (k y x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3383799
       grind)
    | exact superpose eq3383799 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3383799
       grind)
    | exact resolve eq12 eq3383799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383799
  have eq3387229 : (M.op x y) = (M.op y x) ∨ y = (k y x) ∨ (M.op x y) = (k x y) := by grind
  clear eq3387226
  have eq3387370 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq3387229
       grind)
    | exact superpose eq3387229 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3387229
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3387229
       grind)
    | exact resolve eq13 eq3387229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387229
  have eq3387371 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k y x) := by grind
  clear eq3387370
  have eq3387372 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k y x) := by grind
  clear eq3387371
  have eq3387375 : y = (k y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq3387372
       have r₂ := eq12 x y
       grind)
    | exact resolve eq3387372 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387372
  have eq3387379 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq3383545
       have i₂ := eq3387375
       grind)
    | exact superpose eq3387375 eq3383545
    | exact resolve eq3383545 eq3387375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383545 eq3387375
  have eq3387505 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq3387379
  have eq3387516 : y ≠ y ∨ x = y ∨ y = (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq3383829
       have i₂ := eq3387505
       grind)
    | exact superpose eq3387505 eq3383829
    | (have r₁ := eq3383829
       have r₂ := eq3387505
       grind)
    | exact resolve eq3383829 eq3387505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383829
  have eq3387519 : x ≠ y ∨ y = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq3387505
       grind)
    | exact superpose eq3387505 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq3387505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3387528 : y = (M.op y x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq3387516
  have eq3387539 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq3387528
       grind)
    | exact superpose eq3387528 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq3387528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387528
  have eq3387543 : y ≠ (M.op x y) ∨ y = (k x y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq3387539
       have r₂ := eq12 x y
       grind)
    | exact resolve eq3387539 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387539
  have eq3387545 : y ≠ (M.op x y) ∨ y = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq3387543
       have r₂ := eq3387519
       grind)
    | exact resolve eq3387543 eq3387519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387519 eq3387543
  have eq3387546 : y = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq3387545
       have r₂ := eq3387505
       grind)
    | exact resolve eq3387545 eq3387505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387545
  have eq3387667 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq3387546
  have eq3387668 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq3387667
       have r₂ := eq3387505
       grind)
    | exact resolve eq3387667 eq3387505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387505 eq3387667
  have eq3387678 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3158
       have i₂ := eq3387668
       grind)
    | exact superpose eq3387668 eq3158
    | exact resolve eq3158 eq3387668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3158
  have eq3387692 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3387678
  have eq3387762 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3387692
       grind)
    | exact superpose eq3387692 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3387692
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3387692
       grind)
    | exact resolve eq13 eq3387692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387692
  have eq3387763 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq3387762
  have eq3387764 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq3387763
  have eq3387766 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq3387764
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq3387764 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387764
  have eq3387770 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq3387766
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3387766
    | exact resolve eq3387766 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387766
  have eq3387772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3387770
       have i₂ := eq3387668
       grind)
    | exact superpose eq3387668 eq3387770
    | exact resolve eq3387770 eq3387668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387668 eq3387770
  have eq3387773 : False := by grind
  exact eq3387773

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_pyy_pyx_pyy_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq76 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq66
    | exact resolve eq66 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (M.op X1 X1) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq213 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X1 X2
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq183
    | (have j0 := eq183 X0 X1 X2
       grind)
    | exact resolve eq183 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq183
  have eq215 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq181
    | (have j0 := eq181 X0 X1
       grind)
    | exact resolve eq181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq219 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq215 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq215 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq215 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq215 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq222 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq219
    | (have j0 := eq219 X0 X1
       grind)
    | exact resolve eq219 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq219
  have eq482 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq222
    | exact resolve eq222 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq523 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq482 X1 (τ X0)
       grind)
    | exact superpose eq482 eq18
    | (have j1 := eq482 X1 (τ X0)
       grind)
    | exact resolve eq18 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq539 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq523
    | (have j0 := eq523 X0 X1
       grind)
    | exact resolve eq523 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq1651 : ∀ X0 X1 X2 X3 : G, (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k X3 (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op X3 (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (k (σ X0) X1)
       have i₂ := eq213 X0 X1 X2
       grind)
    | exact superpose eq213 eq13
    | (have j0 := eq13 (σ X2) (k (σ X0) X1)
       have j1 := eq213 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq213 X0 X1 X2
       grind)
    | exact resolve eq13 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq5209 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (M.op X1 X1) (τ (M.op X0 X0)))) X0) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 (M.op (M.op X1 X1) (τ (M.op X0 X0)))
       have i₂ := eq136 X0 X1
       grind)
    | exact superpose eq136 eq539
    | exact resolve eq539 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq539
  have eq5350 : ∀ X0 X1 : G, (k (σ (M.op (M.op X1 X1) (τ (M.op X0 X0)))) X0) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5209 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5209
    | (have j0 := eq5209 X0 X1
       grind)
    | exact resolve eq5209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5209
  have eq13690 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X1 X1) (τ (M.op (σ X0) (σ X0)))))) X0) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ (M.op (M.op X1 X1) (τ (M.op (σ X0) (σ X0))))) X0
       have i₂ := eq5350 (σ X0) X1
       grind)
    | exact superpose eq5350 eq23
    | (have j1 := eq5350 (σ X0) X1
       grind)
    | exact resolve eq23 eq5350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5350
  have eq13757 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (M.op X1 X1) (τ (M.op (σ X0) (σ X0)))) X0) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13690 X0 X1
       have i₂ := eq10 (M.op (M.op X1 X1) (τ (M.op (σ X0) (σ X0))))
       grind)
    | exact superpose eq10 eq13690
    | (have j0 := eq13690 X0 X1
       grind)
    | exact resolve eq13690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13690
  have eq13804 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (M.op X1 X1) (τ (σ (M.op X0 X0)))) X0) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13757 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq13757
    | (have j0 := eq13757 X0 X1
       grind)
    | exact resolve eq13757 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13757
  have eq13850 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (M.op X1 X1) (M.op X0 X0)) X0) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13804 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq13804
    | (have j0 := eq13804 X0 X1
       grind)
    | exact resolve eq13804 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13804
  have eq13889 : ∀ X0 X1 : G, (k (M.op (M.op X1 X1) (M.op X0 X0)) X0) = X0 ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13850 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13850
    | (have j0 := eq13850 X0 X1
       grind)
    | exact resolve eq13850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13850
  have eq13907 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k (M.op (M.op X1 X1) (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13889 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq13889
    | (have j0 := eq13889 X0 X1
       grind)
    | exact resolve eq13889 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq13889
  have eq13920 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k (M.op (M.op X1 X1) (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13907 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq13907
    | (have j0 := eq13907 X0 X1
       grind)
    | exact resolve eq13907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13907
  have eq13930 : ∀ X0 X1 : G, (k (M.op (M.op X1 X1) (M.op X0 X0)) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13920 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13920
    | (have j0 := eq13920 X0 X1
       grind)
    | exact resolve eq13920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13920
  have eq14245 : ∀ X0 X1 : G, (k (M.op (τ (M.op X0 X0)) (M.op X1 X1)) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13930 X1 (τ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq13930
    | (have j0 := eq13930 X1 X1
       grind)
    | exact resolve eq13930 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13930
  have eq14781 : ∀ X0 X1 : G, (k (M.op (τ (τ (M.op X0 X0))) (M.op X1 X1)) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14245 (τ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq14245
    | (have j0 := eq14245 X0 X1
       grind)
    | exact resolve eq14245 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14245
  have eq15549 : ∀ X0 X1 : G, (k (M.op (τ (τ (τ (M.op X0 X0)))) (M.op X1 X1)) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14781 (τ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq14781
    | (have j0 := eq14781 X0 X1
       grind)
    | exact resolve eq14781 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14781
  have eq16616 : ∀ X0 X1 : G, (k (M.op (τ (τ (τ (τ (M.op X0 X0))))) (M.op X1 X1)) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15549 (τ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq15549
    | (have j0 := eq15549 X0 X1
       grind)
    | exact resolve eq15549 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15549
  have eq29609 : ∀ X0 X1 : G, (k (M.op (τ (τ (τ (τ (τ (M.op X0 X0)))))) (M.op X1 X1)) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16616 (τ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq16616
    | (have j0 := eq16616 X0 X1
       grind)
    | exact resolve eq16616 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16616
  have eq42131 : ∀ X0 X1 : G, (k (M.op (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))) (M.op X1 X1)) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29609 (τ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq29609
    | (have j0 := eq29609 X0 X1
       grind)
    | exact resolve eq29609 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq29609
  have eq137652 : ∀ X0 X1 X2 : G, (k (σ X1) X2) ≠ (k (σ X1) X2) ∨ (k (σ X0) (k (σ X1) X2)) = (M.op (k (σ X1) X2) (σ X0)) ∨ (k (σ X1) X2) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (k (σ X1) X2) (σ X0)) ∨ (M.op (k (σ X1) X2) (σ X0)) ≠ (M.op (k (σ X1) X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1651 X1 X2 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq137653 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (k (σ X1) X2) (σ X0)) ∨ (k (σ X1) X2) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (k (σ X1) X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq137652 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137652
  have eq137660 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (k (σ X1) X2) (σ X0)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (k (σ X1) X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq137653 X0 X1 X2
       have j1 := eq12 (σ X0) (k (σ X1) X2)
       grind)
    | (have r₁ := eq137653 X0 X1 X2
       have r₂ := eq12 (σ X0) (k (σ X1) X2)
       grind)
    | exact resolve eq137653 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137653
  have eq137732 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (k (σ X1) X2) (σ X0)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (k (σ X1) X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137660 X0 X1 X2
       have i₂ := eq27 X1 X2 X0
       grind)
    | exact superpose eq27 eq137660
    | (have j0 := eq137660 X0 X1 X2
       grind)
    | exact resolve eq137660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq137660
  have eq137733 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (k (σ X1) X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq137732 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137732
  have eq138143 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (k X0 (τ X1))
       have i₂ := eq137733 (τ X2) X0 X1
       grind)
    | exact superpose eq137733 eq17
    | exact resolve eq17 eq137733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq137733
  have eq138482 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138143 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq138143
    | exact resolve eq138143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138143
  have eq138798 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138482 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq138482
    | exact resolve eq138482 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq138482
  have eq139105 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op (k X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138798 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq138798
    | exact resolve eq138798 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138798
  have eq140903 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq139105 X0 X1 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq139105
    | exact resolve eq139105 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq140950 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq139105 (M.op (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))) (M.op X1 X1)) X1 X1
       have i₂ := eq42131 X0 X1
       grind)
    | exact superpose eq42131 eq139105
    | (have j1 := eq42131 X0 X0
       grind)
    | exact resolve eq139105 eq42131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42131 eq139105
  have eq143653 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140903 X0 X1
       have i₂ := eq140950 X0 X1
       grind)
    | exact superpose eq140950 eq140903
    | (have j1 := eq140950 X0 X1
       grind)
    | exact resolve eq140903 eq140950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140903 eq140950
  have eq196734 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq143653 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143653
  have eq196735 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq196734 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196734
  have eq202441 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq196735 (σ X1) (σ X0)
       grind)
    | exact superpose eq196735 eq15
    | exact resolve eq15 eq196735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202742 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq202441 X0 X1
       have i₂ := eq196735 X1 X0
       grind)
    | exact superpose eq196735 eq202441
    | exact resolve eq202441 eq196735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196735 eq202441
  have eq221654 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq202742 x y
       grind)
    | exact superpose eq202742 eq16
    | (have r₁ := eq16
       have r₂ := eq202742 x y
       grind)
    | exact resolve eq16 eq202742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202742
  have eq222158 : False := by grind
  exact eq222158
