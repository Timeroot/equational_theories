import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation1443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 x)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X2 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) ≠ X0 ∨ (M.op (M.op X0 (M.op X0 X2)) (M.op X0 X1)) = (k (M.op X0 (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X2)) (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 X2)) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq75
    | exact resolve eq75 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2111 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (k (σ X1) X2) (σ X0)) ∨ (k (σ X1) X2) = (M.op (σ X0) (k (σ X1) X2)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) ∨ (k (σ X1) X2) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X1) X2) (σ X0)
       have i₂ := eq145 X1 X2 X0
       grind)
    | exact superpose eq145 eq13
    | (have j0 := eq13 (k (σ X1) X2) (σ X0)
       have j1 := eq145 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq145 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq145 X0 X1 X2
       grind)
    | exact resolve eq13 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq2119 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (k (σ X1) X2) (σ X0)) ∨ (k (σ X1) X2) = (M.op (σ X0) (k (σ X1) X2)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2111 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq2120 : ∀ X0 X1 X2 : G, (σ X0) = (k (k (σ X1) X2) (σ X0)) ∨ (k (σ X1) X2) = (M.op (σ X0) (k (σ X1) X2)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2119 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119
  have eq2122 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (σ (k (k X1 (τ X2)) X0)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2120 X0 X1 X2
       have i₂ := eq29 X1 X2 X0
       grind)
    | exact superpose eq29 eq2120
    | (have j0 := eq2120 X0 X1 X2
       grind)
    | exact resolve eq2120 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2120
  have eq4094 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq76 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq4095 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq4094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094
  have eq4100 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4095 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4095
    | (have j0 := eq4095 X0
       grind)
    | exact resolve eq4095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095
  have eq4110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4100 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4100
    | exact resolve eq4100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100
  have eq4151 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4110 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq4110
    | (have j0 := eq4110 X0
       grind)
    | exact resolve eq4110 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4110
  have eq4159 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X0 x
       have i₂ := eq4151 X0
       grind)
    | exact superpose eq4151 eq19
    | (have j1 := eq4151 X0
       grind)
    | exact resolve eq19 eq4151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4163 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0 X0
       have i₂ := eq4151 X0
       grind)
    | exact superpose eq4151 eq67
    | (have j1 := eq4151 X0
       grind)
    | exact resolve eq67 eq4151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4151
  have eq4658 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1 X0
       have i₂ := eq4163 X0
       grind)
    | exact superpose eq4163 eq33
    | (have j1 := eq4163 X0
       grind)
    | (have r₁ := eq33 X0 X1 X0
       have r₂ := eq4163 X0
       grind)
    | exact resolve eq33 eq4163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq4163
  have eq4689 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4658
  have eq19374 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4689 X0 (M.op X0 (M.op X0 x))
       have i₂ := eq4159 X0 x
       grind)
    | exact superpose eq4159 eq4689
    | (have j0 := eq4689 X0 x
       have j1 := eq4159 X0 x
       grind)
    | exact resolve eq4689 eq4159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4159 eq4689
  have eq19463 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq19374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19374
  have eq19634 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq19463 X0
       grind)
    | exact superpose eq19463 eq11
    | (have j1 := eq19463 X0
       grind)
    | exact resolve eq11 eq19463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19463
  have eq19765 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq19634 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq19634
    | (have j0 := eq19634 X0
       grind)
    | exact resolve eq19634 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19634
  have eq19766 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq19765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19765
  have eq20019 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq19766 (τ X0)
       grind)
    | exact superpose eq19766 eq34
    | exact resolve eq34 eq19766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq20089 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20019 X0
       have i₂ := eq19766 X0
       grind)
    | exact superpose eq19766 eq20019
    | exact resolve eq20019 eq19766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20019
  have eq20383 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ X0) (τ X0) x
       have i₂ := eq20089 X0
       grind)
    | exact superpose eq20089 eq19
    | exact resolve eq19 eq20089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20089
  have eq26584 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ (M.op X0 (M.op X0 X1))) (M.op (τ X0) (M.op (τ X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20383 (M.op X0 (M.op X0 X2)) X1
       have i₂ := eq9 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq9 eq20383
    | exact resolve eq20383 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20383
  have eq28669 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (σ X0) (M.op (σ X0) X1))) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26584 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26584
    | exact resolve eq26584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26584
  have eq29139 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (τ (M.op (σ X0) (M.op (σ X0) X1))))) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 (τ (M.op (σ X0) (M.op (σ X0) X1))) (M.op X0 (M.op X0 x)) x
       have i₂ := eq28669 X0 X1 x
       grind)
    | exact superpose eq28669 eq20
    | exact resolve eq20 eq28669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq28669
  have eq40201 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (M.op X0 (k (σ X1) X2)) ∨ (σ (k (k X1 (τ X2)) (τ X0))) = X0 ∨ (σ (k (k X1 (τ X2)) (τ X0))) = (M.op (k (σ X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2122 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2122
    | exact resolve eq2122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq40414 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = X0 ∨ (k (σ X1) X2) = (M.op X0 (k (σ X1) X2)) ∨ (σ (k (k X1 (τ X2)) (τ X0))) = (M.op (k (σ X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40201 X0 X1 X2
       have i₂ := eq18 X0 (k X1 (τ X2))
       grind)
    | exact superpose eq18 eq40201
    | (have j0 := eq40201 X0 X1 X2
       grind)
    | exact resolve eq40201 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40201
  have eq40488 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = X0 ∨ (k (σ X1) X2) = (M.op X0 (k (σ X1) X2)) ∨ (σ (k (k X1 (τ X2)) (τ X0))) = (M.op (k (σ X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40414 X0 X1 X2
       have i₂ := eq18 X2 X1
       grind)
    | exact superpose eq18 eq40414
    | (have j0 := eq40414 X0 X1 X2
       grind)
    | exact resolve eq40414 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40414
  have eq40543 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (k (σ X1) X2) X0) ∨ (k (k (σ X1) X2) X0) = X0 ∨ (k (σ X1) X2) = (M.op X0 (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40488 X0 X1 X2
       have i₂ := eq18 X0 (k X1 (τ X2))
       grind)
    | exact superpose eq18 eq40488
    | (have j0 := eq40488 X0 X1 X2
       grind)
    | exact resolve eq40488 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40488
  have eq40570 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op (k (σ X1) X2) X0) ∨ (k (k (σ X1) X2) X0) = X0 ∨ (k (σ X1) X2) = (M.op X0 (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40543 X0 X1 X2
       have i₂ := eq18 X2 X1
       grind)
    | exact superpose eq18 eq40543
    | (have j0 := eq40543 X0 X1 X2
       grind)
    | exact resolve eq40543 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq40543
  have eq40593 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op (k (σ X1) X2) X0) ∨ (k (k (σ X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq40570 X0 X1 X2
       have j1 := eq12 (k (σ X1) X2) X0
       grind)
    | (have r₁ := eq40570 X1 X1 X2
       have r₂ := eq12 (k (σ X1) X2) X1
       grind)
    | exact resolve eq40570 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40570
  have eq83866 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op (k X0 X1) X2) ∨ (k (k X0 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40593 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40593
    | exact resolve eq40593 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84045 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) X2) ≠ X2 ∨ (k (k (σ X0) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq40593 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40593
  have eq84265 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X2) ≠ X2 ∨ (k (k X0 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84045 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84045
    | exact resolve eq84045 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84045
  have eq84892 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X1 ∨ (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84265 X0 X0 x
       have i₂ := eq19766 X0
       grind)
    | exact superpose eq19766 eq84265
    | exact resolve eq84265 eq19766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84265
  have eq85113 : ∀ X0 X2 : G, (M.op X0 X2) ≠ X2 ∨ (k X0 X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq84892 (M.op X0 (τ (M.op (σ X0) (M.op (σ X0) x)))) x
       have i₂ := eq29139 X0 x (τ (M.op (σ X0) (M.op (σ X0) x)))
       grind)
    | exact superpose eq29139 eq84892
    | exact resolve eq84892 eq29139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84892
  have eq88254 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83866 X0 X0 x
       have i₂ := eq19766 X0
       grind)
    | exact superpose eq19766 eq83866
    | exact resolve eq83866 eq19766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19766 eq83866
  have eq89009 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (k X0 X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq88254 (M.op X0 (τ (M.op (σ X0) (M.op (σ X0) x)))) x
       have i₂ := eq29139 X0 x (τ (M.op (σ X0) (M.op (σ X0) x)))
       grind)
    | exact superpose eq29139 eq88254
    | exact resolve eq88254 eq29139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29139 eq88254
  have eq89388 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq89009 (σ X0) X1
       grind)
    | exact superpose eq89009 eq30
    | (have j1 := eq89009 (σ X0) X1
       grind)
    | exact resolve eq30 eq89009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq90175 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) X0
       have i₂ := eq89388 X1 (σ X0)
       grind)
    | exact superpose eq89388 eq24
    | (have j1 := eq89388 X1 (σ X0)
       grind)
    | exact resolve eq24 eq89388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq89388
  have eq90276 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90175 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq90175
    | (have j0 := eq90175 X0 X1
       grind)
    | exact resolve eq90175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90175
  have eq90370 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90276 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90276
    | (have j0 := eq90276 X0 X1
       grind)
    | exact resolve eq90276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90276
  have eq90428 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90370 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90370
    | (have j0 := eq90370 X0 X1
       grind)
    | exact resolve eq90370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90370
  have eq91455 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq90428 X1 X0
       grind)
    | exact superpose eq90428 eq11
    | (have j1 := eq90428 X1 X0
       grind)
    | exact resolve eq11 eq90428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90428
  have eq91925 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91455 x y
       grind)
    | exact superpose eq91455 eq16
    | (have j1 := eq91455 x y
       grind)
    | exact resolve eq16 eq91455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91455
  have eq92913 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq91925
       have i₂ := eq89009 x y
       grind)
    | exact superpose eq89009 eq91925
    | (have j1 := eq89009 x y
       grind)
    | exact resolve eq91925 eq89009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89009
  have eq92914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq91925
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq91925
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq91925 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91925
  have eq92918 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq92914
  have eq92919 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq92918
  have eq92920 : y = (M.op x y) ∨ y = (k x y) := by grind
  clear eq92913
  have eq92922 : y = (k x y) := by
    first
    | (have j1 := eq85113 x y
       grind)
    | (have r₁ := eq92920
       have r₂ := eq85113 x y
       grind)
    | exact resolve eq92920 eq85113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85113 eq92920
  have eq92932 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq158 x y
       have i₂ := eq92922
       grind)
    | exact superpose eq92922 eq158
    | (have j0 := eq158 x y
       grind)
    | exact resolve eq158 eq92922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq92951 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq92932
  have eq93419 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq92919
       grind)
    | exact superpose eq92919 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq92919
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq92919
       grind)
    | exact resolve eq12 eq92919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92919
  have eq93478 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq93419
  have eq93480 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93478
       have i₂ := eq92922
       grind)
    | exact superpose eq92922 eq93478
    | exact resolve eq93478 eq92922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93478
  have eq93481 : y = (M.op x y) := by grind
  clear eq93480
  have eq164240 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92951
       grind)
    | exact superpose eq92951 eq16
    | exact resolve eq16 eq92951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92951
  have eq164392 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq164240
       have i₂ := eq93481
       grind)
    | exact superpose eq93481 eq164240
    | exact resolve eq164240 eq93481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164240
  have eq164393 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq164392
  have eq165034 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq164393
       grind)
    | exact superpose eq164393 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq164393
       grind)
    | exact resolve eq12 eq164393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164393
  have eq165095 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq165034
  have eq165126 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq165095
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq165095
    | exact resolve eq165095 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165095
  have eq165173 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq165126
       have i₂ := eq92922
       grind)
    | exact superpose eq92922 eq165126
    | exact resolve eq165126 eq92922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92922 eq165126
  have eq170053 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq165173
       grind)
    | exact superpose eq165173 eq16
    | exact resolve eq16 eq165173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165173
  have eq170195 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq170053
       have i₂ := eq93481
       grind)
    | exact superpose eq93481 eq170053
    | exact resolve eq170053 eq93481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93481 eq170053
  have eq170196 : False := by grind
  exact eq170196

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation1443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
    | (have r₁ := eq56 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq63 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq57 (τ X0)
       grind)
    | exact superpose eq57 eq18
    | exact resolve eq18 eq57
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
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq60
    | exact resolve eq60 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq66
    | exact resolve eq66 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq66
  have eq83 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq431 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq461 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq431 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq431
    | (have j0 := eq431 X0 X1
       grind)
    | exact resolve eq431 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq431
  have eq465 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq461 X0 X1
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq461 X0 X0
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq461 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq469 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq465
    | (have j0 := eq465 X0 X1
       grind)
    | exact resolve eq465 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq465
  have eq677 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq469
    | exact resolve eq469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq469 (σ X0) X1
       grind)
    | exact superpose eq469 eq15
    | (have j1 := eq469 (σ X0) X1
       grind)
    | exact resolve eq15 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq708 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq689
    | (have j0 := eq689 X0 X1
       grind)
    | exact resolve eq689 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq726 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq677 (τ X1) X0
       grind)
    | exact superpose eq677 eq18
    | (have j1 := eq677 (τ X1) X0
       grind)
    | exact resolve eq18 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq677
  have eq1344 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq726
    | exact resolve eq726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq1393 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1344 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1344
    | (have j0 := eq1344 X0 X1
       grind)
    | exact resolve eq1344 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq12569 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq708 x y
       grind)
    | exact superpose eq708 eq16
    | (have j1 := eq708 x y
       grind)
    | exact resolve eq16 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12684 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq708 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq12946 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq12569
       have i₂ := eq1393 y x
       grind)
    | exact superpose eq1393 eq12569
    | (have j1 := eq1393 y x
       grind)
    | (have r₁ := eq12569
       have r₂ := eq1393 y x
       grind)
    | exact resolve eq12569 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12569
  have eq12947 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12946
  have eq12952 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq12947
       grind)
    | exact superpose eq12947 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12947
       grind)
    | exact resolve eq13 eq12947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12947
  have eq13002 : (k x y) = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12952
  have eq62597 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12684 x y
       have i₂ := eq13002
       grind)
    | exact superpose eq13002 eq12684
    | (have j0 := eq12684 x y
       grind)
    | exact resolve eq12684 eq13002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12684 eq13002
  have eq62608 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) := by grind
  clear eq62597
  have eq62609 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) := by grind
  clear eq62608
  have eq63021 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62609
       grind)
    | exact superpose eq62609 eq16
    | exact resolve eq16 eq62609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63024 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq83 x (σ y)
       have i₂ := eq62609
       grind)
    | exact superpose eq62609 eq83
    | (have j0 := eq83 x (σ y)
       grind)
    | (have r₁ := eq83 x (σ y)
       have r₂ := eq62609
       grind)
    | exact resolve eq83 eq62609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq62609
  have eq63121 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq63024
  have eq63149 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq63121
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq63121
    | exact resolve eq63121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63121
  have eq63159 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq63149
       have i₂ := eq69 y
       grind)
    | exact superpose eq69 eq63149
    | exact resolve eq63149 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq63149
  have eq63559 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1393 y x
       have i₂ := eq63159
       grind)
    | exact superpose eq63159 eq1393
    | (have j0 := eq1393 y x
       grind)
    | exact resolve eq1393 eq63159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63159
  have eq63749 : (M.op x y) = (M.op x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq63559
       have r₂ := eq63021
       grind)
    | exact resolve eq63559 eq63021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63559
  have eq64209 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq63021
       have i₂ := eq63749
       grind)
    | exact superpose eq63749 eq63021
    | exact resolve eq63021 eq63749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63749
  have eq64276 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq64209
  have eq64277 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq64276
  have eq64283 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq84 y X0
       have i₂ := eq64277
       grind)
    | exact superpose eq64277 eq84
    | (have j0 := eq84 y X0
       grind)
    | (have r₁ := eq84 y x
       have r₂ := eq64277
       grind)
    | exact resolve eq84 eq64277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64277
  have eq64451 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq64283 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64283
  have eq64533 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq64451 X0
       have j1 := eq84 y X0
       grind)
    | (have r₁ := eq64451 X0
       have r₂ := eq84 y x
       grind)
    | exact resolve eq64451 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq64451
  have eq64988 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq64533 (σ X0)
       grind)
    | exact superpose eq64533 eq15
    | exact resolve eq15 eq64533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64533
  have eq66166 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64988 x
       grind)
    | exact superpose eq64988 eq16
    | exact resolve eq16 eq64988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64988
  have eq66743 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq66166
       have i₂ := eq1393 y x
       grind)
    | exact superpose eq1393 eq66166
    | (have j1 := eq1393 y x
       grind)
    | (have r₁ := eq66166
       have r₂ := eq1393 y x
       grind)
    | exact resolve eq66166 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq66744 : (M.op x y) = (M.op x x) := by grind
  clear eq66743
  have eq67050 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq63021
       have i₂ := eq66744
       grind)
    | exact superpose eq66744 eq63021
    | exact resolve eq63021 eq66744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63021 eq66744
  have eq67116 : y = (M.op y y) := by grind
  clear eq67050
  have eq67117 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq67116
       grind)
    | exact superpose eq67116 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq67116
       grind)
    | exact resolve eq12 eq67116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67116
  have eq67290 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq67117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67117
  have eq67953 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq66166
       have i₂ := eq67290 x
       grind)
    | exact superpose eq67290 eq66166
    | exact resolve eq66166 eq67290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66166 eq67290
  have eq67961 : False := by grind
  exact eq67961

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation1443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq724 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq724 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq766 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq765 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq874 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq766 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq877 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq874 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq874 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq874 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq874 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq874 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq929 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq877 X0 (τ X1)
       grind)
    | exact superpose eq877 eq19
    | (have j1 := eq877 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq932 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq877 (σ X0) (σ X1)
       grind)
    | exact superpose eq877 eq15
    | (have j1 := eq877 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq1012 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq929
    | exact resolve eq929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq1053 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1012 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1012
    | (have j0 := eq1012 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq1012 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1220 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq932 x y
       grind)
    | exact superpose eq932 eq16
    | (have j1 := eq932 x y
       grind)
    | exact resolve eq16 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq1254 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1220
       have i₂ := eq1053 y x
       grind)
    | exact superpose eq1053 eq1220
    | (have j1 := eq1053 (σ x) (σ y)
       grind)
    | (have r₁ := eq1220
       have r₂ := eq1053 y x
       grind)
    | (have r₁ := eq1220
       have r₂ := eq1053 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1220
       have r₂ := eq1053 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1220 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053 eq1220
  have eq1255 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1254
  have eq1259 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1255
       grind)
    | exact superpose eq1255 eq10
    | exact resolve eq10 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1302 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1259
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1259
    | exact resolve eq1259 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1303 : x = y := by grind
  clear eq1302
  have eq1305 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1303
       grind)
    | exact superpose eq1303 eq16
    | exact resolve eq16 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq1306 : False := by grind
  exact eq1306

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq78 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq44
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq44 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ x) (σ y)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq79
    | (have r₁ := eq79
       have r₂ := eq131
       grind)
    | exact resolve eq79 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq131
  have eq685 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq684
  have eq954 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq685 eq122
    | exact resolve eq122 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq958 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq954
  have eq963 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq958
       have r₂ := eq133
       grind)
    | exact resolve eq958 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq958
  have eq979 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq963 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq963
       grind)
    | exact resolve eq13 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq989 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq979
  have eq1001 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq989
    | exact resolve eq989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1001 eq122
    | exact resolve eq122 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq1001
  have eq1134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1131
  have eq1138 : x = (M.op x y) := by
    first
    | (have r₁ := eq1134
       have r₂ := eq27
       grind)
    | exact resolve eq1134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1141 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1138 eq20
    | exact resolve eq20 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1147 : x ≠ x ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq1138 eq78
    | (have r₁ := eq78
       have r₂ := eq1138
       grind)
    | exact resolve eq78 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1152 : x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq1147
  have eq1158 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1141
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1141
    | exact resolve eq1141 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1159 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1158 eq26
    | exact resolve eq26 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1469 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1152
       grind)
    | exact superpose eq1152 eq44
    | exact resolve eq44 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1476 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1158 eq1469
    | exact resolve eq1469 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1478 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1476
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1476
    | exact resolve eq1476 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1479 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1158 eq1478
    | exact resolve eq1478 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq1483 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1479 eq96
    | (have j0 := eq96 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq96 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1484 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1483
  have eq1486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1159 eq1484
    | exact resolve eq1484 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1489 : x = (M.op y x) := by
    first
    | (have r₁ := eq1486
       have r₂ := eq27
       grind)
    | exact resolve eq1486 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486
  have eq1499 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1489
       grind)
    | exact superpose eq1489 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1489
       grind)
    | exact resolve eq13 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1509 : (M.op x y) = (k x y) := by grind
  clear eq1499
  have eq1511 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1509
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1509
    | exact resolve eq1509 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1509
  have eq1516 : x = (k x y) := by
    first
    | exact superpose eq1138 eq1511
    | exact resolve eq1511 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138 eq1511
  have eq1545 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1516
       grind)
    | exact superpose eq1516 eq44
    | exact resolve eq44 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1516
  have eq1552 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1158 eq1545
    | exact resolve eq1545 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq1554 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1552
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1552
    | exact resolve eq1552 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1552
  have eq1555 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1158 eq1554
    | exact resolve eq1554 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq1554
  have eq1608 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1555 eq96
    | (have j0 := eq96 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq96 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1555
  have eq1609 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1608
  have eq1611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1159 eq1609
    | exact resolve eq1609 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159 eq1609
  have eq1614 : False := by grind
  exact eq1614

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq49
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq139 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq143 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       have j1 := eq58 X0 X1
       grind)
    | (have r₁ := eq139 X0 X1
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq139 X1 X1
       have r₂ := eq58 X1 X1
       grind)
    | exact resolve eq139 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq139
  have eq327 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq143 (σ X0) (σ X1)
       grind)
    | exact superpose eq143 eq15
    | exact resolve eq15 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 X1
       have i₂ := eq143 X0 X1
       grind)
    | exact superpose eq143 eq327
    | exact resolve eq327 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq327
  have eq336 : False := by grind
  exact eq336

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxy_x_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
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
  clear eq22
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X2)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X0 (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq93 x y
       grind)
    | exact superpose eq93 eq44
    | (have j1 := eq93 x y
       grind)
    | exact resolve eq44 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq586 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 X1) X0 (M.op (M.op X0 (M.op X1 x)) x)
       have i₂ := eq52 X0 X1 x x
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq117 eq93
    | (have j0 := eq93 x (σ y)
       grind)
    | exact resolve eq93 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq843
    | exact resolve eq843 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq847 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq844
       have r₂ := eq27
       grind)
    | exact resolve eq844 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq852 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq847 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq847
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq847
       grind)
    | exact resolve eq13 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq860 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq852
  have eq890 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq860 eq87
    | exact resolve eq87 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq860
  have eq894 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq890
    | exact resolve eq890 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq890
  have eq909 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq93 y y
       have i₂ := eq894
       grind)
    | exact superpose eq894 eq93
    | (have j0 := eq93 x y
       grind)
    | exact resolve eq93 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq910 : y = (M.op y y) := by grind
  clear eq909
  have eq916 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq910
       grind)
    | exact superpose eq910 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq910
       grind)
    | exact resolve eq13 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : ∀ X0 : G, (M.op (M.op X0 y) (M.op X0 y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq910
       grind)
    | exact superpose eq910 eq14
    | exact resolve eq14 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq55 y y X0
       have i₂ := eq910
       grind)
    | exact superpose eq910 eq55
    | exact resolve eq55 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq926 : y = (k y y) := by grind
  clear eq916
  have eq932 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq926
       grind)
    | exact superpose eq926 eq76
    | exact resolve eq76 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq926
  have eq936 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq932
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq932
    | exact resolve eq932 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq932
  have eq951 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq936 eq93
    | (have j0 := eq93 x (σ y)
       grind)
    | exact resolve eq93 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq936
  have eq952 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq951
  have eq960 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq952 eq14
    | exact resolve eq14 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq963 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq952 eq55
    | exact resolve eq55 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1091 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq918 (M.op y (M.op y X0))
       have i₂ := eq921 X0
       grind)
    | exact superpose eq921 eq918
    | exact resolve eq918 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq1105 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1091 X0
       have i₂ := eq910
       grind)
    | exact superpose eq910 eq1091
    | exact resolve eq1091 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1300 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq963 eq960
    | exact resolve eq960 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1314 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq952 eq1300
    | exact resolve eq1300 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1442 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq586 y X0
       have i₂ := eq1105 X0
       grind)
    | exact superpose eq1105 eq586
    | exact resolve eq586 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1444 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1314 eq586
    | exact resolve eq586 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq1314
  have eq1469 : ∀ X0 : G, (M.op y X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq918 (M.op y X0)
       have i₂ := eq1442 X0
       grind)
    | exact superpose eq1442 eq918
    | exact resolve eq918 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq1442
  have eq1483 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq1469 X0
       have i₂ := eq910
       grind)
    | exact superpose eq910 eq1469
    | exact resolve eq1469 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq1469
  have eq1497 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1483 X0
       grind)
    | exact superpose eq1483 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1483 X0
       grind)
    | exact resolve eq13 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq1527 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1497 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1537 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1527 x
       grind)
    | exact superpose eq1527 eq44
    | exact resolve eq44 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1527
  have eq1548 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1537
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1537
    | exact resolve eq1537 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1537
  have eq1550 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1548
    | exact resolve eq1548 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1548
  have eq1567 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1444 eq960
    | exact resolve eq960 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq1444
  have eq1581 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq952 eq1567
    | exact resolve eq1567 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq1567
  have eq1595 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1581 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1581 X0
       grind)
    | exact resolve eq13 eq1581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1625 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1595 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1625 eq1550
    | exact resolve eq1550 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq1625
  have eq1651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1640
    | exact resolve eq1640 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1640
  have eq1659 : False := by grind
  exact eq1659

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pxx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (M.op X0 X1) (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) (M.op X0 (M.op X1 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op X0 X1) X0 X0
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq63
    | exact resolve eq63 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq473 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq476 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq720 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq468 x y
       grind)
    | exact superpose eq468 eq16
    | (have j1 := eq468 x y
       grind)
    | exact resolve eq16 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq742 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq468 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq742 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq744 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq746 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq744 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq744
    | (have j0 := eq744 X0
       grind)
    | exact resolve eq744 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq4207 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq476 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq476
    | exact resolve eq476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq4254 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4207 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4207
    | (have j0 := eq4207 X0 X1
       grind)
    | exact resolve eq4207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4207
  have eq4407 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  clear eq746
  have eq4409 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4407 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4407
    | (have j0 := eq4407 X0
       grind)
    | exact resolve eq4407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4407
  have eq4543 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq473 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq473
    | exact resolve eq473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq4630 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4543 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq4543
    | (have j0 := eq4543 X0 X1
       grind)
    | exact resolve eq4543 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4543
  have eq4662 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (σ (k (τ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (k X0 X1) X2
       have i₂ := eq4630 X0 X1
       grind)
    | exact superpose eq4630 eq18
    | (have j1 := eq4630 X0 X1
       grind)
    | exact resolve eq18 eq4630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4630
  have eq4770 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (k (M.op X0 X1) (σ X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4662 X0 X1 X2
       have i₂ := eq18 (M.op X0 X1) X2
       grind)
    | exact superpose eq18 eq4662
    | (have j0 := eq4662 X0 X1 X2
       grind)
    | exact resolve eq4662 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4662
  have eq15741 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  clear eq4409
  have eq15819 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq15741 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq15741
    | (have j0 := eq15741 X0
       grind)
    | exact resolve eq15741 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15741
  have eq15820 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq15819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15819
  have eq15851 : ∀ X0 : G, (σ (k (σ (k X0 X0)) (σ X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15820 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq15820
    | exact resolve eq15820 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15870 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 (σ (τ X0))) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15820 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq15820
    | exact resolve eq15820 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15972 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq15870 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15870
    | exact resolve eq15870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15870
  have eq15984 : ∀ X0 : G, (σ (σ (k (k X0 X0) X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15851 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq15851
    | exact resolve eq15851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15851
  have eq16002 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq15972 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq15972
    | exact resolve eq15972 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15972
  have eq16024 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k (σ (τ X0)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16002 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq16002
    | exact resolve eq16002 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16002
  have eq16041 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16024 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16024
    | exact resolve eq16024 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16024
  have eq16092 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16041 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq16041
    | exact resolve eq16041 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16115 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4770 (σ X0) (σ X0) X0
       have i₂ := eq16041 (σ X0)
       grind)
    | exact superpose eq16041 eq4770
    | (have j0 := eq4770 (σ X0) (σ X0) x
       grind)
    | exact resolve eq4770 eq16041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4770
  have eq16166 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq16115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16115
  have eq16214 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16166 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq16166
    | (have j0 := eq16166 X0
       grind)
    | exact resolve eq16166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16166
  have eq16234 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16092 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq16092
    | exact resolve eq16092 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16092
  have eq16281 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16214 X0
       have i₂ := eq15820 X0
       grind)
    | exact superpose eq15820 eq16214
    | (have j0 := eq16214 X0
       grind)
    | exact resolve eq16214 eq15820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15820 eq16214
  have eq16295 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16234 X0
       have i₂ := eq16041 X0
       grind)
    | exact superpose eq16041 eq16234
    | exact resolve eq16234 eq16041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16234
  have eq16336 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16281 X0
       have i₂ := eq16041 X0
       grind)
    | exact superpose eq16041 eq16281
    | (have j0 := eq16281 X0
       grind)
    | exact resolve eq16281 eq16041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16281
  have eq16372 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq16336
  have eq17516 : ∀ X0 : G, (σ (σ (k (σ (k X0 X0)) (σ X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15984 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq15984
    | exact resolve eq15984 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15984
  have eq17726 : ∀ X0 : G, (σ (σ (σ (k (k X0 X0) X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17516 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq17516
    | exact resolve eq17516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17516
  have eq17764 : ∀ X0 : G, (σ (σ (σ (M.op (k X0 X0) X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17726 X0
       have i₂ := eq16041 X0
       grind)
    | exact superpose eq16041 eq17726
    | exact resolve eq17726 eq16041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16041 eq17726
  have eq21638 : ∀ X0 : G, (σ (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0))))) = (M.op (σ (σ (k X0 (σ (τ X0))))) (σ (σ (σ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq17764 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq17764
    | exact resolve eq17764 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17764
  have eq21751 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq21638 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21638
    | exact resolve eq21638 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21638
  have eq21787 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (M.op (τ (k X0 X0)) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq21751 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq21751
    | exact resolve eq21751 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21751
  have eq21813 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (τ (M.op (k X0 X0) X0))))) := by
    intro X0
    first
    | (have i₁ := eq21787 X0
       have i₂ := eq16295 X0
       grind)
    | exact superpose eq16295 eq21787
    | exact resolve eq21787 eq16295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21787
  have eq21834 : ∀ X0 : G, (σ (σ (M.op (k X0 X0) X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq21813 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq21813
    | exact resolve eq21813 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21813
  have eq21898 : ∀ X0 : G, (M.op (σ (σ (k (τ X0) (τ X0)))) (σ X0)) = (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq21834 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21834
    | exact resolve eq21834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21834
  have eq22009 : ∀ X0 : G, (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) = (M.op (σ (σ (τ (k X0 X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21898 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq21898
    | exact resolve eq21898 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21898
  have eq22044 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq22009 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq22009
    | exact resolve eq22009 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22009
  have eq22070 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (τ (M.op (k X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq22044 X0
       have i₂ := eq16295 X0
       grind)
    | exact superpose eq16295 eq22044
    | exact resolve eq22044 eq16295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22044
  have eq22090 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq22070 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq22070
    | exact resolve eq22070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22070
  have eq28613 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq720
       have i₂ := eq4254 x y
       grind)
    | exact superpose eq4254 eq720
    | (have j1 := eq4254 (σ x) (σ y)
       grind)
    | (have r₁ := eq720
       have r₂ := eq4254 x y
       grind)
    | exact resolve eq720 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq4254
  have eq28614 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq28613
  have eq34182 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op (k X0 X0) X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq16372 X0
       grind)
    | exact superpose eq16372 eq64
    | (have j1 := eq16372 X0
       grind)
    | exact resolve eq64 eq16372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq34183 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69 (σ X0) (σ X0)
       have i₂ := eq16372 X0
       grind)
    | exact superpose eq16372 eq69
    | (have j1 := eq16372 X0
       grind)
    | exact resolve eq69 eq16372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq16372
  have eq35476 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (k (τ X0) (τ X0)) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34182 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34182
    | exact resolve eq34182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34182
  have eq35622 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ (k X0 X0)) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35476 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq35476
    | (have j0 := eq35476 X0
       grind)
    | exact resolve eq35476 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35476
  have eq35649 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (τ (M.op (k X0 X0) X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35622 X0
       have i₂ := eq16295 X0
       grind)
    | exact superpose eq16295 eq35622
    | (have j0 := eq35622 X0
       grind)
    | exact resolve eq35622 eq16295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35622
  have eq35669 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35649 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq35649
    | (have j0 := eq35649 X0
       grind)
    | exact resolve eq35649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35649
  have eq39387 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34183 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34183
    | exact resolve eq34183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34183
  have eq39530 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (τ (k X0 X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39387 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq39387
    | (have j0 := eq39387 X0
       grind)
    | exact resolve eq39387 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq39387
  have eq39544 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (τ (M.op (k X0 X0) X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39530 X0
       have i₂ := eq16295 X0
       grind)
    | exact superpose eq16295 eq39530
    | (have j0 := eq39530 X0
       grind)
    | exact resolve eq39530 eq16295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16295 eq39530
  have eq39553 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39544 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq39544
    | (have j0 := eq39544 X0
       grind)
    | exact resolve eq39544 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39544
  have eq39587 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 (k X0 X0) X0 X0
       have i₂ := eq39553 X0
       grind)
    | exact superpose eq39553 eq63
    | (have j1 := eq39553 X0
       grind)
    | exact resolve eq63 eq39553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq39553
  have eq39831 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39587 (σ x)
       have i₂ := eq468 x x
       grind)
    | exact superpose eq468 eq39587
    | (have j0 := eq39587 (σ X0)
       have j1 := eq468 X0 X0
       grind)
    | exact resolve eq39587 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq39587
  have eq39927 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39831 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39831
  have eq39938 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39927 X0
       have j1 := eq743 X0
       grind)
    | (have r₁ := eq39927 X0
       have r₂ := eq743 X0
       grind)
    | exact resolve eq39927 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq39927
  have eq39942 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39938 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq39938
    | (have j0 := eq39938 X0
       grind)
    | exact resolve eq39938 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39938
  have eq45169 : ∀ X0 : G, (σ (τ X0)) = (M.op (k X0 (σ (τ X0))) (M.op (σ (τ X0)) (k X0 (σ (τ X0))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39942 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq39942
    | (have j0 := eq39942 (τ X0)
       grind)
    | exact resolve eq39942 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq39942
  have eq45287 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq45169 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45169
    | (have j0 := eq45169 X0
       grind)
    | exact resolve eq45169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45169
  have eq45343 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45287 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45287
    | (have j0 := eq45287 X0
       grind)
    | exact resolve eq45287 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45287
  have eq45814 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 (k X0 X0) (M.op X0 (k X0 X0))
       have i₂ := eq45343 X0
       grind)
    | exact superpose eq45343 eq76
    | (have j1 := eq45343 X0
       grind)
    | exact resolve eq76 eq45343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45343
  have eq46614 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35669 X0
       have i₂ := eq45814 X0
       grind)
    | exact superpose eq45814 eq35669
    | (have j0 := eq35669 X0
       have j1 := eq45814 X0
       grind)
    | exact resolve eq35669 eq45814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35669 eq45814
  have eq46757 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46614 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46614
  have eq47195 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46757 (σ X0)
       grind)
    | exact superpose eq46757 eq15
    | (have j1 := eq46757 (σ X0)
       grind)
    | exact resolve eq15 eq46757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46757
  have eq49398 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq47195
  have eq49463 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49398 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq49398
    | (have j0 := eq49398 X0
       grind)
    | exact resolve eq49398 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49398
  have eq49464 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq49463 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49463
  have eq49541 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49464 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49464
    | exact resolve eq49464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49854 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq49541 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq49541
    | exact resolve eq49541 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq49541
  have eq49932 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq49854 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49854
    | exact resolve eq49854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49854
  have eq50175 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22090 X0
       have i₂ := eq49932 X0
       grind)
    | exact superpose eq49932 eq22090
    | exact resolve eq22090 eq49932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22090
  have eq612352 : x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq89 x y
       have i₂ := eq28614
       grind)
    | exact superpose eq28614 eq89
    | exact resolve eq89 eq28614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq612489 : (σ x) = (σ (k y y)) ∨ x = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq612352
       have i₂ := eq49464 y
       grind)
    | exact superpose eq49464 eq612352
    | exact resolve eq612352 eq49464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612352
  have eq612578 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq612489
       have i₂ := eq49932 y
       grind)
    | exact superpose eq49932 eq612489
    | exact resolve eq612489 eq49932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612489
  have eq1173822 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq612578
       have i₂ := eq28614
       grind)
    | exact superpose eq28614 eq612578
    | exact resolve eq612578 eq28614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28614 eq612578
  have eq1173974 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1173822
  have eq1174015 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1173974
       have i₂ := eq49464 y
       grind)
    | exact superpose eq49464 eq1173974
    | exact resolve eq1173974 eq49464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173974
  have eq1174016 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1174015
       have i₂ := eq49932 y
       grind)
    | exact superpose eq49932 eq1174015
    | exact resolve eq1174015 eq49932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174015
  have eq1174017 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1174016
  have eq1174111 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76 (σ x) (σ y)
       have i₂ := eq1174017
       grind)
    | exact superpose eq1174017 eq76
    | exact resolve eq76 eq1174017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1184183 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1174111
       have i₂ := eq1174017
       grind)
    | exact superpose eq1174017 eq1174111
    | exact resolve eq1174111 eq1174017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174017 eq1174111
  have eq1184370 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1184183
  have eq1184422 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1184370
       have i₂ := eq49464 y
       grind)
    | exact superpose eq49464 eq1184370
    | exact resolve eq1184370 eq49464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49464 eq1184370
  have eq1184452 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1184422
       have i₂ := eq49932 y
       grind)
    | exact superpose eq49932 eq1184422
    | exact resolve eq1184422 eq49932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49932 eq1184422
  have eq1184453 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1184452
  have eq1184610 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1184453
       grind)
    | exact superpose eq1184453 eq10
    | exact resolve eq10 eq1184453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184453
  have eq1185198 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1184610
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1184610
    | exact resolve eq1184610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184610
  have eq1185199 : x = (M.op y y) := by grind
  clear eq1185198
  have eq1185558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50175 y
       have i₂ := eq1185199
       grind)
    | exact superpose eq1185199 eq50175
    | exact resolve eq50175 eq1185199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50175 eq1185199
  have eq1185935 : False := by grind
  exact eq1185935

/-- `Equation1458`: `x = (x ◇ y) ◇ (y ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_pxy_pyx_Equation1458 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1458 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1458.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X2 X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) X2
       have i₂ := eq9 X0 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33 X1 (M.op X0 (M.op (M.op X1 X2) X3)) X2
       have i₂ := eq33 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq33 eq33
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq33 X2 X0 x
       grind)
    | exact superpose eq33 eq9
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38 X2 (M.op X0 (M.op X1 X3)) X1
       have i₂ := eq33 X1 X0 X3
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq203 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ X0 ∨ (M.op X1 X3) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 (M.op X1 X3)
       have i₂ := eq43 X0 X1 X3 X2
       grind)
    | (have i₁ := eq12 X0 (M.op X1 X3)
       have i₂ := eq43 X0 X1 X2 X3
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 X0 (M.op X1 X2)
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq508 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X2 (σ X1) (σ X0)
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq38
    | (have j1 := eq76 X1 X0
       grind)
    | exact resolve eq38 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq524 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq509 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq525 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq524 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq524 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq524 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq524 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq526 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq508 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq508 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq508 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq508 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq529 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq525
    | (have j0 := eq525 X0 X1
       grind)
    | exact resolve eq525 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq530 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq526 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq526
    | (have j0 := eq526 X0 X1
       grind)
    | exact resolve eq526 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq634 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq530 (τ X0) (τ X1)
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq530
    | (have j0 := eq530 (τ X0) (τ X1)
       grind)
    | exact resolve eq530 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq643 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq634
    | (have j0 := eq634 X0 X1
       grind)
    | exact resolve eq634 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq649 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq643
    | (have j0 := eq643 X0 X1
       grind)
    | exact resolve eq643 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq652 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq649 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq649
    | (have j0 := eq649 X0 X1
       grind)
    | exact resolve eq649 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq653 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq652
    | (have j0 := eq652 X0 X1
       grind)
    | exact resolve eq652 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq654 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq653
    | (have j0 := eq653 X0 X1
       grind)
    | exact resolve eq653 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq655 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq654
    | (have j0 := eq654 X0 X1
       grind)
    | exact resolve eq654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq656 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq655 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq655
    | (have j0 := eq655 X0 X1
       grind)
    | exact resolve eq655 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq733 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq767 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq733 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq733
    | (have j0 := eq733 X0 X1
       grind)
    | exact resolve eq733 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq891 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq521 (τ X1) (τ X0)
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq521
    | (have j0 := eq521 (τ X1) (τ X0)
       grind)
    | exact resolve eq521 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq891 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq891
    | (have j0 := eq891 X0 X1
       grind)
    | exact resolve eq891 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq901 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq898 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq898
    | (have j0 := eq898 X0 X1
       grind)
    | exact resolve eq898 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq903 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq901 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq901
    | (have j0 := eq901 X0 X1
       grind)
    | exact resolve eq901 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq904 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq903 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq903
    | (have j0 := eq903 X0 X1
       grind)
    | exact resolve eq903 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq905 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq904 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq904
    | (have j0 := eq904 X0 X1
       grind)
    | exact resolve eq904 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq906 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq905 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq905
    | (have j0 := eq905 X0 X1
       grind)
    | exact resolve eq905 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq927 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq505
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq505
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq505 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq928 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq927
  have eq1000 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq529 (τ X1) (τ X0)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq529
    | (have j0 := eq529 (τ X0) (τ X1)
       grind)
    | exact resolve eq529 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1008 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1000 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1000
    | (have j0 := eq1000 X0 X1
       grind)
    | exact resolve eq1000 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1011 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1008 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1008
    | (have j0 := eq1008 X0 X1
       grind)
    | exact resolve eq1008 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1013 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1011 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1011
    | (have j0 := eq1011 X0 X1
       grind)
    | exact resolve eq1011 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1014 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1013 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1013
    | (have j0 := eq1013 X0 X1
       grind)
    | exact resolve eq1013 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1015 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1014 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1014
    | (have j0 := eq1014 X0 X1
       grind)
    | exact resolve eq1014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1016 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1015 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1015
    | (have j0 := eq1015 X0 X1
       grind)
    | exact resolve eq1015 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1017 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1016 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1016
    | (have j0 := eq1016 X0 X1
       grind)
    | exact resolve eq1016 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq8987 : y ≠ y ∨ x = (k y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq928
       grind)
    | exact superpose eq928 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq928
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq928
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq928
       grind)
    | exact resolve eq12 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq9017 : x = (k y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8987
  have eq12438 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq515 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq12439 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq12438 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12438
  have eq35511 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ (k (τ X0) (τ X0))) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12439 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12439
    | exact resolve eq12439 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12439
  have eq35629 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35511 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq35511
    | (have j0 := eq35511 X0 X1
       grind)
    | exact resolve eq35511 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35511
  have eq35634 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35629 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35629
    | (have j0 := eq35629 X0 X1
       grind)
    | exact resolve eq35629 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35629
  have eq35771 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 X0 (k X0 X0) x
       have i₂ := eq35634 X0 x
       grind)
    | exact superpose eq35634 eq33
    | (have j1 := eq35634 X0 x
       grind)
    | exact resolve eq33 eq35634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35634
  have eq36147 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35771 (σ X0)
       grind)
    | exact superpose eq35771 eq15
    | (have j1 := eq35771 (σ X0)
       grind)
    | exact resolve eq15 eq35771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35771
  have eq36573 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq36147 X0
       grind)
    | exact superpose eq36147 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq36147 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq36147 X0
       grind)
    | exact resolve eq12 eq36147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36602 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq36147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36147
  have eq36610 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq36573 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36573
  have eq36616 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36610 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq36610
    | (have j0 := eq36610 X0
       grind)
    | exact resolve eq36610 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36610
  have eq36634 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq36616 X0
       have j1 := eq36602 X0
       grind)
    | (have r₁ := eq36616 X0
       have r₂ := eq36602 X0
       grind)
    | exact resolve eq36616 eq36602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36602 eq36616
  have eq36641 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36634 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36634
    | exact resolve eq36634 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36781 : ∀ X0 X1 : G, (M.op (M.op X1 (σ (k X0 X0))) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) X1 (σ X0)
       have i₂ := eq36634 X0
       grind)
    | exact superpose eq36634 eq33
    | exact resolve eq33 eq36634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36785 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X0) X1 (σ X0)
       have i₂ := eq36634 X0
       grind)
    | exact superpose eq36634 eq38
    | exact resolve eq38 eq36634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36891 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq36641 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq36641
    | exact resolve eq36641 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq36641
  have eq36915 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq36891 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36891
    | exact resolve eq36891 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36891
  have eq38846 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k (k X0 X0) (k X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq36781 X0 (σ (k X0 X0))
       have i₂ := eq36634 (k X0 X0)
       grind)
    | exact superpose eq36634 eq36781
    | exact resolve eq36781 eq36634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36781
  have eq38999 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op (k X0 X0) (k X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq38846 X0
       have i₂ := eq36915 (k X0 X0)
       grind)
    | exact superpose eq36915 eq38846
    | exact resolve eq38846 eq36915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38846
  have eq39101 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq38999 X0
       have i₂ := eq36915 X0
       grind)
    | exact superpose eq36915 eq38999
    | exact resolve eq38999 eq36915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38999
  have eq39184 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39101 X0
       have i₂ := eq38 X0 X0 X0
       grind)
    | exact superpose eq38 eq39101
    | exact resolve eq39101 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39101
  have eq39403 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X0) X1 (σ X0)
       have i₂ := eq39184 X0
       grind)
    | exact superpose eq39184 eq38
    | exact resolve eq38 eq39184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39407 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X1 (σ X0) X2 (σ X0)
       have i₂ := eq39184 X0
       grind)
    | exact superpose eq39184 eq43
    | exact resolve eq43 eq39184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40138 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ X0 ∨ (σ (k X1 X1)) = (k (M.op X0 (σ X1)) (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (σ X1)) (σ (k X1 X1))
       have i₂ := eq36785 X1 X0
       grind)
    | exact superpose eq36785 eq12
    | (have j0 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq12 eq36785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36785
  have eq40194 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ X0 ∨ (σ (M.op X1 X1)) = (k (M.op X0 (σ X1)) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40138 X0 X0
       have i₂ := eq36915 X0
       grind)
    | exact superpose eq36915 eq40138
    | (have j0 := eq40138 X0 X1
       grind)
    | exact resolve eq40138 eq36915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40138
  have eq245633 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq521 x y
       have i₂ := eq9017
       grind)
    | exact superpose eq9017 eq521
    | (have j0 := eq521 x y
       grind)
    | exact resolve eq521 eq9017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9017
  have eq245682 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq245633
  have eq245683 : x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq245682
  have eq358137 : x ≠ x ∨ y = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq245683
       grind)
    | exact superpose eq245683 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq245683
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq245683
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq245683
       grind)
    | exact resolve eq12 eq245683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245683
  have eq358268 : y = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq358137
  have eq362155 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq521 y x
       have i₂ := eq358268
       grind)
    | exact superpose eq358268 eq521
    | (have j0 := eq521 y x
       grind)
    | exact resolve eq521 eq358268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq358268
  have eq362201 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq362155
  have eq362202 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq362201
  have eq362275 : (σ y) ≠ (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40194 (σ y) x
       have i₂ := eq362202
       grind)
    | exact superpose eq362202 eq40194
    | (have r₁ := eq40194 (σ y) x
       have r₂ := eq362202
       grind)
    | (have r₁ := eq40194 (σ x) y
       have r₂ := eq362202
       grind)
    | exact resolve eq40194 eq362202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40194
  have eq362278 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq362202
       grind)
    | exact superpose eq362202 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq362202
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq362202
       grind)
    | exact resolve eq12 eq362202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362279 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq362202
       grind)
    | exact superpose eq362202 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq362202
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq362202
       grind)
    | exact resolve eq13 eq362202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362290 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (σ y) X1 (σ x)
       have i₂ := eq362202
       grind)
    | exact superpose eq362202 eq43
    | exact resolve eq43 eq362202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362202
  have eq362408 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq362279
  have eq362409 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq362408
  have eq362410 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq362278
  have eq362411 : (σ (M.op x x)) = (k (σ y) (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq362275
  have eq362439 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq362409
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq362409
    | exact resolve eq362409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362409
  have eq362440 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq362410
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq362410
    | exact resolve eq362410 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362410
  have eq362441 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (σ (k y (M.op x x))) := by
    first
    | (have i₁ := eq362411
       have i₂ := eq15 y (M.op x x)
       grind)
    | exact superpose eq15 eq362411
    | exact resolve eq362411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362411
  have eq362483 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq362440
       grind)
    | exact superpose eq362440 eq16
    | exact resolve eq16 eq362440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362528 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq362440
       grind)
    | exact superpose eq362440 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq362440
       grind)
    | exact resolve eq12 eq362440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362529 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq362440
       grind)
    | exact superpose eq362440 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq362440
       grind)
    | exact resolve eq13 eq362440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362440
  have eq362658 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq362529
  have eq362659 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq362528
  have eq362687 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq362658
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq362658
    | exact resolve eq362658 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362658
  have eq362688 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq362659
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq362659
    | exact resolve eq362659 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362659
  have eq362718 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq529 y x
       grind)
    | (have r₁ := eq362687
       have r₂ := eq529 y x
       grind)
    | exact resolve eq362687 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362687
  have eq364452 : (k y x) = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq362688
       grind)
    | exact superpose eq362688 eq10
    | exact resolve eq10 eq362688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362688
  have eq364828 : x = (k y x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq364452
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq364452
    | exact resolve eq364452 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364452
  have eq366590 : x ≠ x ∨ y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq656 y x
       have i₂ := eq364828
       grind)
    | exact superpose eq364828 eq656
    | (have j0 := eq656 y x
       grind)
    | (have r₁ := eq656 y x
       have r₂ := eq364828
       grind)
    | exact resolve eq656 eq364828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq364828
  have eq366621 : y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq366590
  have eq379079 : y = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq366621
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq366621
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq366621 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366621
  have eq379141 : y = (M.op y x) ∨ (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) := by grind
  clear eq379079
  have eq383959 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq379141
       grind)
    | exact superpose eq379141 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq379141
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq379141
       grind)
    | exact resolve eq13 eq379141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379141
  have eq384088 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y x)) := by grind
  clear eq383959
  have eq384089 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y x)) := by grind
  clear eq384088
  have eq386443 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq39403 y (σ x)
       have i₂ := eq362439
       grind)
    | exact superpose eq362439 eq39403
    | exact resolve eq39403 eq362439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39403
  have eq386447 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq362439
       grind)
    | exact superpose eq362439 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq362439
       grind)
    | exact resolve eq12 eq362439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386454 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (σ x) (σ y)
       have i₂ := eq362439
       grind)
    | exact superpose eq362439 eq38
    | exact resolve eq38 eq362439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362439
  have eq386579 : (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq386447
  have eq386607 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq386579
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq386579
    | exact resolve eq386579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386579
  have eq389230 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq386607
       grind)
    | exact superpose eq386607 eq16
    | exact resolve eq16 eq386607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389300 : (σ x) ≠ (σ (k x y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq386607
       grind)
    | exact superpose eq386607 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq386607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389453 : (σ y) = (σ (k x y)) ∨ (σ x) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq389300
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq389300
    | exact resolve eq389300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389300
  have eq389454 : (σ x) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq389453
  have eq392613 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq362718
       grind)
    | exact superpose eq362718 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq362718
       grind)
    | exact resolve eq12 eq362718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362718
  have eq392745 : (σ x) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by grind
  clear eq392613
  have eq392773 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq392745
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq392745
    | exact resolve eq392745 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392745
  have eq394273 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq392773
       grind)
    | exact superpose eq392773 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq392773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392773
  have eq394426 : (σ x) = (σ (k y x)) ∨ (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq394273
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq394273
    | exact resolve eq394273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394273
  have eq394427 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq394426
  have eq395676 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq394427
       have i₂ := eq767 y x
       grind)
    | exact superpose eq767 eq394427
    | (have j1 := eq767 y x
       grind)
    | exact resolve eq394427 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq394427
  have eq427909 : ∀ X0 X1 X2 : G, (σ x) = (M.op (σ x) (M.op (σ y) X0)) ∨ (M.op X1 (σ y)) = (M.op X1 (M.op (σ y) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 (σ x) (σ y)
       have i₂ := eq362290 X1 X2
       grind)
    | exact superpose eq362290 eq38
    | (have j1 := eq362290 X1 X2
       grind)
    | exact resolve eq38 eq362290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443457 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x x)) = (σ (k y (M.op x x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq362441
       grind)
    | exact superpose eq362441 eq16
    | exact resolve eq16 eq362441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362441
  have eq496402 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq389230
       have i₂ := eq384089
       grind)
    | exact superpose eq384089 eq389230
    | exact resolve eq389230 eq384089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384089 eq389230
  have eq496522 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op y x)) := by grind
  clear eq496402
  have eq525460 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq362483
       have i₂ := eq496522
       grind)
    | exact superpose eq496522 eq362483
    | exact resolve eq362483 eq496522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362483 eq496522
  have eq525613 : (σ y) = (σ (M.op y x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq525460
  have eq620733 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq386443
       grind)
    | exact superpose eq386443 eq16
    | exact resolve eq16 eq386443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386443
  have eq841325 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq427909 X0 (σ x) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427909
  have eq841352 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq841325 X0
       have j1 := eq362290 (σ x) X0
       grind)
    | (have r₁ := eq841325 X0
       have r₂ := eq362290 X0 x
       grind)
    | exact resolve eq841325 eq362290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362290 eq841325
  have eq841527 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq39407 y (σ x) x
       have i₂ := eq841352 x
       grind)
    | exact superpose eq841352 eq39407
    | exact resolve eq39407 eq841352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39407
  have eq841533 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq33 (σ y) (σ x) x
       have i₂ := eq841352 x
       grind)
    | exact superpose eq841352 eq33
    | exact resolve eq33 eq841352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844806 : ∀ X0 : G, (σ x) = (M.op (σ (k x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq841533
       have i₂ := eq386454 X0
       grind)
    | exact superpose eq386454 eq841533
    | (have j1 := eq386454 X0
       grind)
    | exact resolve eq841533 eq386454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386454 eq841533
  have eq845018 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (k x y)) (σ y)) := by
    first
    | (have i₁ := eq844806 x
       have i₂ := eq841352 x
       grind)
    | exact superpose eq841352 eq844806
    | exact resolve eq844806 eq841352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841352 eq844806
  have eq848318 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ (k x y)) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq845018
       grind)
    | exact superpose eq845018 eq16
    | exact resolve eq16 eq845018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845018
  have eq1920477 : (M.op y x) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op y x)
       have i₂ := eq525613
       grind)
    | exact superpose eq525613 eq10
    | exact resolve eq10 eq525613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525613
  have eq1921006 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1920477
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1920477
    | exact resolve eq1920477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920477
  have eq1923578 : y ≠ y ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1921006
       grind)
    | exact superpose eq1921006 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1921006
       grind)
    | exact resolve eq12 eq1921006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921006
  have eq1923852 : x = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq1923578
  have eq1923870 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1923852
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1923852
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1923852 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923852
  have eq1923952 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq1923870
  have eq1923963 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1923952
       have r₂ := eq395676
       grind)
    | exact resolve eq1923952 eq395676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395676 eq1923952
  have eq1926427 : ∀ X0 : G, x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 y x
       have i₂ := eq1923963
       grind)
    | exact superpose eq1923963 eq38
    | exact resolve eq38 eq1923963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923963
  have eq1933867 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ (M.op x x)) = (σ (k y (M.op x x))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq443457
       have i₂ := eq1926427 X0
       grind)
    | exact superpose eq1926427 eq443457
    | (have j1 := eq1926427 X0
       grind)
    | (have r₁ := eq443457
       have r₂ := eq1926427 X0
       grind)
    | exact resolve eq443457 eq1926427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926427
  have eq1934189 : ∀ X0 : G, (σ (M.op x x)) = (σ (k y (M.op x x))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq1933867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933867
  have eq1934227 : ∀ X0 : G, (σ (M.op x x)) = (σ (k y (M.op x x))) ∨ y = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq1934189 X0
       grind)
    | (have r₁ := eq1934189 X0
       have r₂ := eq443457
       grind)
    | exact resolve eq1934189 eq443457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443457 eq1934189
  have eq2002124 : ∀ X0 : G, (k y (M.op x x)) = (τ (σ (M.op x x))) ∨ y = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k y (M.op x x))
       have i₂ := eq1934227 X0
       grind)
    | exact superpose eq1934227 eq10
    | (have j1 := eq1934227 X0
       grind)
    | exact resolve eq10 eq1934227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934227
  have eq2002688 : ∀ X0 : G, (M.op x x) = (k y (M.op x x)) ∨ y = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq2002124 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq2002124
    | (have j0 := eq2002124 X0
       grind)
    | exact resolve eq2002124 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002124
  have eq2002759 : (M.op x x) = (k y (M.op x x)) := by
    first
    | (have j1 := eq203 y x x x
       grind)
    | (have r₁ := eq2002688 x
       have r₂ := eq203 y x x x
       grind)
    | exact resolve eq2002688 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq2002688
  have eq2006679 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op x x) y) ∨ y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq906 y (M.op x x)
       have i₂ := eq2002759
       grind)
    | exact superpose eq2002759 eq906
    | (have j0 := eq906 y (M.op x x)
       grind)
    | (have r₁ := eq906 y (M.op x x)
       have r₂ := eq2002759
       grind)
    | exact resolve eq906 eq2002759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq2006698 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y (M.op x x)) ∨ y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq1017 y (M.op x x)
       have i₂ := eq2002759
       grind)
    | exact superpose eq2002759 eq1017
    | (have j0 := eq1017 y (M.op x x)
       grind)
    | (have r₁ := eq1017 y (M.op x x)
       have r₂ := eq2002759
       grind)
    | exact resolve eq1017 eq2002759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002759
  have eq2006729 : y = (M.op y (M.op x x)) ∨ (M.op x x) = (M.op y (M.op x x)) := by grind
  clear eq2006698
  have eq2006732 : (M.op x x) = (M.op (M.op x x) y) ∨ y = (M.op y (M.op x x)) := by grind
  clear eq2006679
  have eq2010764 : (M.op x x) = (M.op y (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq33 x y x
       have i₂ := eq2006729
       grind)
    | exact superpose eq2006729 eq33
    | exact resolve eq33 eq2006729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2010767 : ∀ X0 : G, (M.op x x) = (M.op y (M.op x x)) ∨ y = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq43 y x X0 x
       have i₂ := eq2006729
       grind)
    | exact superpose eq2006729 eq43
    | exact resolve eq43 eq2006729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2010789 : ∀ X0 : G, (M.op x x) = (M.op y (M.op x x)) ∨ (M.op (M.op X0 y) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq38 (M.op x x) X0 y
       have i₂ := eq2006729
       grind)
    | exact superpose eq2006729 eq38
    | exact resolve eq38 eq2006729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006729
  have eq2011207 : ∀ X0 : G, y = (M.op y x) ∨ (M.op (M.op X0 (M.op x x)) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 y X0 (M.op x x)
       have i₂ := eq2010764
       grind)
    | exact superpose eq2010764 eq33
    | exact resolve eq33 eq2010764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2025347 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x x)) y) = X1 ∨ y = (M.op y (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 y x
       have i₂ := eq2011207 X1
       grind)
    | exact superpose eq2011207 eq38
    | (have j1 := eq2011207 X1
       grind)
    | exact resolve eq38 eq2011207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011207
  have eq2043114 : ∀ X0 : G, y = (M.op y (M.op x x)) ∨ (M.op X0 x) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq37 X0 x x y
       have i₂ := eq2006732
       grind)
    | exact superpose eq2006732 eq37
    | exact resolve eq37 eq2006732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq2048544 : y ≠ (M.op x x) ∨ y = (M.op y (M.op x x)) := by
    first
    | (have j0 := eq2010767 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010767
  have eq2056056 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 x) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq33 x y x
       have i₂ := eq2043114 X0
       grind)
    | exact superpose eq2043114 eq33
    | (have j1 := eq2043114 X0
       grind)
    | exact resolve eq33 eq2043114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2056059 : ∀ X0 X1 : G, y = (M.op y (M.op x X0)) ∨ (M.op X1 x) = (M.op X1 (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 y x X0 x
       have i₂ := eq2043114 X1
       grind)
    | exact superpose eq2043114 eq43
    | (have j1 := eq2043114 X1
       grind)
    | exact resolve eq43 eq2043114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043114
  have eq2071311 : y ≠ (M.op y x) ∨ (M.op y x) = (M.op y (M.op x x)) := by
    first
    | (have j0 := eq2056059 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056059
  have eq2071344 : (M.op y x) = (M.op y (M.op x x)) := by
    first
    | (have j1 := eq2056056 y
       grind)
    | (have r₁ := eq2071311
       have r₂ := eq2056056 x
       grind)
    | exact resolve eq2071311 eq2056056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056056 eq2071311
  have eq2072767 : ∀ X0 : G, (M.op y x) = (M.op x x) ∨ (M.op (M.op X0 y) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq2010789 X0
       have i₂ := eq2071344
       grind)
    | exact superpose eq2071344 eq2010789
    | (have j0 := eq2010789 X0
       grind)
    | exact resolve eq2010789 eq2071344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010789
  have eq2072790 : ∀ X0 : G, (M.op y x) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq43 y x X0 x
       have i₂ := eq2071344
       grind)
    | exact superpose eq2071344 eq43
    | exact resolve eq43 eq2071344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2080046 : ∀ X0 X1 : G, y = (M.op (M.op x x) (M.op x X0)) ∨ (M.op (M.op X1 y) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 y x
       have i₂ := eq2072767 X1
       grind)
    | exact superpose eq2072767 eq38
    | (have j1 := eq2072767 X1
       grind)
    | exact resolve eq38 eq2072767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072767
  have eq2080344 : ∀ X1 : G, (M.op (M.op X1 y) y) = X1 ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq2080046 x X1
       have i₂ := eq38 x x x
       grind)
    | exact superpose eq38 eq2080046
    | (have j0 := eq2080046 x X1
       grind)
    | exact resolve eq2080046 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080046
  have eq2082917 : ∀ X0 X1 : G, x = y ∨ (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 (M.op X0 y) y
       have i₂ := eq2080344 X0
       grind)
    | exact superpose eq2080344 eq38
    | exact resolve eq38 eq2080344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080344
  have eq2083263 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq2082917 X0 X1
       grind)
    | exact superpose eq2082917 eq16
    | (have j1 := eq2082917 X0 X1
       grind)
    | exact resolve eq16 eq2082917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082917
  have eq2084510 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2083263 X0 X1
       grind)
    | (have r₁ := eq2083263 X0 X1
       have r₂ := eq39184 x
       grind)
    | exact resolve eq2083263 eq39184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083263
  have eq2087118 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq38 x X0 y
       have i₂ := eq2084510 (M.op X0 y) x
       grind)
    | exact superpose eq2084510 eq38
    | exact resolve eq38 eq2084510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2084510
  have eq2148871 : ∀ X0 : G, y = (M.op (M.op x x) y) ∨ y = (M.op y (M.op x X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2025347 X0 y
       have i₂ := eq2010764
       grind)
    | exact superpose eq2010764 eq2025347
    | (have j0 := eq2025347 X0 x
       grind)
    | exact resolve eq2025347 eq2010764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010764 eq2025347
  have eq2149325 : y = (M.op y x) ∨ y = (M.op (M.op x x) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2148871 x
       have i₂ := eq2072790 x
       grind)
    | exact superpose eq2072790 eq2148871
    | exact resolve eq2148871 eq2072790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072790 eq2148871
  have eq2149326 : y = (M.op (M.op x x) y) ∨ y = (M.op y x) := by grind
  clear eq2149325
  have eq2149546 : y = (M.op x x) ∨ y = (M.op y (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2006732
       have i₂ := eq2149326
       grind)
    | exact superpose eq2149326 eq2006732
    | exact resolve eq2006732 eq2149326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006732 eq2149326
  have eq2150016 : y = (M.op y (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq2149546
       have r₂ := eq2048544
       grind)
    | exact resolve eq2149546 eq2048544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048544 eq2149546
  have eq2150057 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2150016
       have i₂ := eq2071344
       grind)
    | exact superpose eq2071344 eq2150016
    | exact resolve eq2150016 eq2071344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071344 eq2150016
  have eq2150058 : y = (M.op y x) := by grind
  clear eq2150057
  have eq2151986 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2150058
       grind)
    | exact superpose eq2150058 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2150058
       grind)
    | exact resolve eq13 eq2150058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2152258 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq2151986
  have eq2158205 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ (M.op y y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq620733
       have i₂ := eq2152258
       grind)
    | exact superpose eq2152258 eq620733
    | exact resolve eq620733 eq2152258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620733 eq2152258
  have eq2158380 : (σ x) = (M.op (σ x) (σ (M.op y y))) ∨ x = (M.op x y) := by grind
  clear eq2158205
  have eq2158409 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2158380
       have i₂ := eq841527
       grind)
    | exact superpose eq841527 eq2158380
    | exact resolve eq2158380 eq841527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841527 eq2158380
  have eq2167879 : x ≠ x ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2158409
       grind)
    | exact superpose eq2158409 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2158409
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2158409
       grind)
    | exact resolve eq12 eq2158409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2158409
  have eq2168154 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2167879
  have eq2168243 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq529 x y
       have i₂ := eq2168154
       grind)
    | exact superpose eq2168154 eq529
    | (have j0 := eq529 x y
       grind)
    | exact resolve eq529 eq2168154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq2168154
  have eq2168322 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2168243
  have eq2168323 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2168322
  have eq2352097 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq2168323
       have i₂ := eq386607
       grind)
    | exact superpose eq386607 eq2168323
    | exact resolve eq2168323 eq386607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386607 eq2168323
  have eq2352629 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq2352097
  have eq2352817 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq2352629
       have r₂ := eq389454
       grind)
    | exact resolve eq2352629 eq389454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389454 eq2352629
  have eq2357191 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq2352817
       grind)
    | exact superpose eq2352817 eq10
    | exact resolve eq10 eq2352817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2357867 : y = (k x y) := by
    first
    | (have i₁ := eq2357191
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2357191
    | exact resolve eq2357191 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357191
  have eq2358108 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1017 x y
       have i₂ := eq2357867
       grind)
    | exact superpose eq2357867 eq1017
    | (have j0 := eq1017 x y
       grind)
    | (have r₁ := eq1017 x y
       have r₂ := eq2357867
       grind)
    | exact resolve eq1017 eq2357867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017 eq2357867
  have eq2358139 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2358108
  have eq2362346 : ∀ X0 : G, (M.op (M.op X0 y) x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq33 x X0 y
       have i₂ := eq2358139
       grind)
    | exact superpose eq2358139 eq33
    | exact resolve eq33 eq2358139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq2362610 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq2384373 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2362346 x
       have i₂ := eq2358139
       grind)
    | exact superpose eq2358139 eq2362346
    | exact resolve eq2362346 eq2358139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358139 eq2362346
  have eq2384763 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2384373
       have r₂ := eq2362610
       grind)
    | exact resolve eq2384373 eq2362610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384373
  have eq2384796 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2384763
       have i₂ := eq2150058
       grind)
    | exact superpose eq2150058 eq2384763
    | exact resolve eq2384763 eq2150058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150058 eq2384763
  have eq2384813 : x = (M.op x y) := by
    first
    | (have r₁ := eq2384796
       have r₂ := eq2362610
       grind)
    | exact resolve eq2384796 eq2362610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362610 eq2384796
  have eq2388032 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ (k x y)) (σ y)) := by
    first
    | (have i₁ := eq848318
       have i₂ := eq2384813
       grind)
    | exact superpose eq2384813 eq848318
    | exact resolve eq848318 eq2384813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848318
  have eq2388405 : (σ x) = (M.op (σ (k x y)) (σ y)) := by grind
  clear eq2388032
  have eq2388483 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2388405
       have i₂ := eq2352817
       grind)
    | exact superpose eq2352817 eq2388405
    | exact resolve eq2388405 eq2352817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352817 eq2388405
  have eq2388506 : (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq2388483
       have i₂ := eq36634 y
       grind)
    | exact superpose eq36634 eq2388483
    | exact resolve eq2388483 eq36634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36634 eq2388483
  have eq2388516 : (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2388506
       have i₂ := eq36915 y
       grind)
    | exact superpose eq36915 eq2388506
    | exact resolve eq2388506 eq36915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36915 eq2388506
  have eq2388671 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2388516
       grind)
    | exact superpose eq2388516 eq10
    | exact resolve eq10 eq2388516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388516
  have eq2389399 : x = (M.op y y) := by
    first
    | (have i₁ := eq2388671
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2388671
    | exact resolve eq2388671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388671
  have eq2393457 : y = (M.op x y) := by
    first
    | (have i₁ := eq2087118 y
       have i₂ := eq2389399
       grind)
    | exact superpose eq2389399 eq2087118
    | exact resolve eq2087118 eq2389399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087118 eq2389399
  have eq2394063 : x = y := by
    first
    | (have i₁ := eq2393457
       have i₂ := eq2384813
       grind)
    | exact superpose eq2384813 eq2393457
    | exact resolve eq2393457 eq2384813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384813 eq2393457
  have eq2394277 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2394063
       grind)
    | exact superpose eq2394063 eq16
    | exact resolve eq16 eq2394063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394063
  have eq2395533 : False := by grind
  exact eq2395533
