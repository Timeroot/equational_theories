import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pyy_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op (M.op (M.op X1 X0) (M.op X2 X0)) (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X2 X0)) X0 X3
       have i₂ := eq9 X0 X1 X2
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
  clear eq18
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq139 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq79 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq144 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq145 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq144 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq144 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq144 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq195 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op (M.op (M.op X1 X0) (M.op X2 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 X1 X2 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X1 X2)) = (M.op (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X2 X1 X1 (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X1 X2)))
       have i₂ := eq195 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq195 eq19
    | exact resolve eq19 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq195
  have eq3716 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op (σ X2) X0) = X0 ∨ (k X2 (τ X0)) = (τ (M.op X0 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq80 X0 X2
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq80 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq80 (σ X1) X1
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3756 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq80 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq3757 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756
  have eq3758 : ∀ X0 X1 X2 : G, (k X2 (τ X0)) = (τ (M.op X0 (σ X2))) ∨ (M.op (σ X2) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3716 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716
  have eq3760 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3757 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3757
    | (have j0 := eq3757 X0
       grind)
    | exact resolve eq3757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3757
  have eq3816 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3760 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3760
    | exact resolve eq3760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3760
  have eq3860 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3816 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq3816
    | (have j0 := eq3816 X0
       grind)
    | exact resolve eq3816 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816
  have eq3863 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3860 X0
       grind)
    | exact superpose eq3860 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq3860 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3860 X0
       grind)
    | exact resolve eq12 eq3860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3860
  have eq3903 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3863 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863
  have eq3982 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3903 X0 X1
       grind)
    | exact superpose eq3903 eq11
    | (have j1 := eq3903 X0 X1
       grind)
    | exact resolve eq11 eq3903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3903
  have eq4090 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3982 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3982
    | (have j0 := eq3982 X0 X0
       grind)
    | exact resolve eq3982 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3982
  have eq4175 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4090 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4090
  have eq4176 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4175 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4175
  have eq4380 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq145 X0 X1
       have i₂ := eq4176 X0
       grind)
    | exact superpose eq4176 eq145
    | (have j0 := eq145 X0 X1
       grind)
    | exact resolve eq145 eq4176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq4417 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4176 (σ X0)
       grind)
    | exact superpose eq4176 eq15
    | exact resolve eq15 eq4176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4481 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4417 X0
       have i₂ := eq4176 X0
       grind)
    | exact superpose eq4176 eq4417
    | exact resolve eq4417 eq4176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176 eq4417
  have eq4828 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq4481 X0
       grind)
    | exact superpose eq4481 eq9
    | exact resolve eq9 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4829 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq4481 X0
       grind)
    | exact superpose eq4481 eq9
    | exact resolve eq9 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20245 : ∀ X0 X1 X2 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3758 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3758
    | (have j0 := eq3758 X1 X2 X2
       grind)
    | exact resolve eq3758 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3758
  have eq20407 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20245 X0 X1 X2
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq20245
    | (have j0 := eq20245 X0 X1 X2
       grind)
    | exact resolve eq20245 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq20245
  have eq20513 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq20407 X1 X0 X2
       grind)
    | exact superpose eq20407 eq11
    | (have j1 := eq20407 X1 X0 X2
       grind)
    | exact resolve eq11 eq20407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20407
  have eq20652 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20513 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq20513
    | (have j0 := eq20513 X0 X1 X1
       grind)
    | exact resolve eq20513 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20513
  have eq21187 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq20652 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20652
  have eq21188 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq21187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21187
  have eq21318 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq21188 (σ X1) (σ X0)
       grind)
    | exact superpose eq21188 eq15
    | (have j1 := eq21188 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq21188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21322 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq21188 (τ X1) X0
       grind)
    | exact superpose eq21188 eq17
    | (have j1 := eq21188 (τ X1) X0
       grind)
    | exact resolve eq17 eq21188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq21188
  have eq22542 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21322 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21322
    | exact resolve eq21322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21322
  have eq22697 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22542 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq22542
    | (have j0 := eq22542 X0 X1
       grind)
    | exact resolve eq22542 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22542
  have eq24227 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21318 x y
       grind)
    | exact superpose eq21318 eq16
    | (have j1 := eq21318 x y
       grind)
    | exact resolve eq16 eq21318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21318
  have eq24505 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq24227
       have i₂ := eq22697 y x
       grind)
    | exact superpose eq22697 eq24227
    | (have j1 := eq22697 (σ y) (σ x)
       grind)
    | (have r₁ := eq24227
       have r₂ := eq22697 y x
       grind)
    | exact resolve eq24227 eq22697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22697 eq24227
  have eq24508 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq24505
  have eq24892 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 x))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq24508
       grind)
    | exact superpose eq24508 eq9
    | exact resolve eq9 eq24508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24953 : x = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq24892 y
       have i₂ := eq24508
       grind)
    | exact superpose eq24508 eq24892
    | exact resolve eq24892 eq24508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24508
  have eq25016 : x = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq24953
  have eq25407 : x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq24892 x
       have i₂ := eq25016
       grind)
    | exact superpose eq25016 eq24892
    | exact resolve eq24892 eq25016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24892 eq25016
  have eq25472 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq25407
  have eq25492 : (σ x) = (M.op (σ x) (M.op (σ (M.op x x)) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4828 x (σ y)
       have i₂ := eq25472
       grind)
    | exact superpose eq25472 eq4828
    | exact resolve eq4828 eq25472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828
  have eq25493 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (M.op x x)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4829 x (σ y)
       have i₂ := eq25472
       grind)
    | exact superpose eq25472 eq4829
    | exact resolve eq4829 eq25472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4829
  have eq25543 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op X1 (σ x))))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq440 X0 (σ y) (σ x) x
       have i₂ := eq25472
       grind)
    | exact superpose eq25472 eq440
    | exact resolve eq440 eq25472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq25472
  have eq25559 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25543 x x
       have i₂ := eq9 (σ x) x x
       grind)
    | exact superpose eq9 eq25543
    | exact resolve eq25543 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25543
  have eq25579 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25559
       have i₂ := eq4481 x
       grind)
    | exact superpose eq4481 eq25559
    | exact resolve eq25559 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25559
  have eq33271 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25492
       have i₂ := eq25579
       grind)
    | exact superpose eq25579 eq25492
    | exact resolve eq25492 eq25579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25492 eq25579
  have eq33344 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by grind
  clear eq33271
  have eq33595 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25493
       have i₂ := eq33344
       grind)
    | exact superpose eq33344 eq25493
    | exact resolve eq25493 eq33344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25493 eq33344
  have eq33667 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq33595
  have eq33676 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33667
       have i₂ := eq4481 x
       grind)
    | exact superpose eq4481 eq33667
    | exact resolve eq33667 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4481 eq33667
  have eq33977 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq33676
       grind)
    | exact superpose eq33676 eq10
    | exact resolve eq10 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33676
  have eq34102 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33977
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33977
    | exact resolve eq33977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33977
  have eq34103 : x = (M.op x x) := by grind
  clear eq34102
  have eq34117 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq34103
       grind)
    | exact superpose eq34103 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq34103
       grind)
    | exact resolve eq12 eq34103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34126 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4380 x X0
       have i₂ := eq34103
       grind)
    | exact superpose eq34103 eq4380
    | (have j0 := eq4380 x X0
       grind)
    | exact resolve eq4380 eq34103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4380 eq34103
  have eq34221 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq34126 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34126
  have eq34225 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq34117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34117
  have eq36030 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq34221 (σ X0)
       grind)
    | exact superpose eq34221 eq15
    | exact resolve eq15 eq34221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34221
  have eq36125 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq36030 X0
       have i₂ := eq34225 X0
       grind)
    | exact superpose eq34225 eq36030
    | exact resolve eq36030 eq34225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34225 eq36030
  have eq38032 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36125 y
       grind)
    | exact superpose eq36125 eq16
    | (have r₁ := eq16
       have r₂ := eq36125 y
       grind)
    | exact resolve eq16 eq36125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36125
  have eq38178 : False := by grind
  exact eq38178

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_x_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op y (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq93
    | (have j0 := eq93 (σ X0) (σ X1)
       grind)
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq93 y x
       grind)
    | exact superpose eq93 eq71
    | (have j1 := eq93 y x
       grind)
    | exact resolve eq71 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119 eq93
    | (have j0 := eq93 (σ y) (σ x)
       grind)
    | exact resolve eq93 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq123
       have r₂ := eq27
       grind)
    | exact resolve eq123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq93 sF1 (σ X0)
       grind)
    | exact superpose eq93 eq37
    | (have j1 := eq93 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq174 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq219 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op X0 (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq128 eq51
    | exact resolve eq51 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq75
    | (have r₁ := eq75
       have r₂ := eq128
       grind)
    | exact resolve eq75 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq372 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq371
  have eq375 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq372 eq119
    | exact resolve eq119 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq378 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq375
  have eq388 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq378 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq378
       grind)
    | exact resolve eq13 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq391 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq388 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq425 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq97 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq97 X0 X0
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq97 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq431 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq425 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq425 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq391 eq119
    | exact resolve eq119 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq391
  have eq459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq456
  have eq464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq459
    | exact resolve eq459 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq466 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq464
       have r₂ := eq27
       grind)
    | exact resolve eq464 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq469 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq466 eq29
    | exact resolve eq29 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq466 eq40
    | exact resolve eq40 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq516 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq471
    | exact resolve eq471 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq471
  have eq518 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq469
    | exact resolve eq469 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq521 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq518 eq50
    | exact resolve eq50 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : y = (M.op y (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq518 eq219
    | exact resolve eq219 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq518
  have eq1282 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (σ (k X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq516 eq16
    | exact resolve eq16 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq1303 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1282 X0
       have i₂ := eq16 (k X0 y)
       grind)
    | exact superpose eq16 eq1282
    | exact resolve eq1282 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1860 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq521 y
       have i₂ := eq528
       grind)
    | exact superpose eq528 eq521
    | exact resolve eq521 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq528
  have eq1871 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1860
  have eq1876 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1871
       grind)
    | exact resolve eq13 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1883 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1876 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq1964 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1883 y
       grind)
    | exact superpose eq1883 eq72
    | exact resolve eq72 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1883
  have eq2278 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1964
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq1964
    | exact resolve eq1964 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq2295 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2278
  have eq2297 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2295
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2295
    | exact resolve eq2295 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2298 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq466 eq2297
    | exact resolve eq2297 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq2311 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2297 eq93
    | (have j0 := eq93 (σ y) (σ y)
       grind)
    | exact resolve eq93 eq2297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq2312 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2311
  have eq2324 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2298
  have eq2332 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2312 eq228
    | exact resolve eq228 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq2334 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2312 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq2312
       grind)
    | exact resolve eq13 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312
  have eq2341 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2342 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq2332
  have eq2348 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2342
    | exact resolve eq2342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq2666 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2324 eq174
    | exact resolve eq174 eq2324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq2324
  have eq2672 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2666
    | exact resolve eq2666 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2666
  have eq2802 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq2348
    | exact resolve eq2348 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq2348
  have eq2813 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2802
  have eq2939 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq429 x y
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq429
    | (have j0 := eq429 x y
       grind)
    | exact resolve eq429 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq2961 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2939
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2939
    | exact resolve eq2939 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939
  have eq3008 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2961
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2961
    | exact resolve eq2961 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2961
  have eq3049 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3008
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3008
    | exact resolve eq3008 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008
  have eq3073 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3049
    | exact resolve eq3049 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049
  have eq3272 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2672 eq93
    | (have j0 := eq93 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq93 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672
  have eq3273 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3272
  have eq3381 : ∀ X0 : G, (σ X0) ≠ (σ (k (M.op x y) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq3462 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3273 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq3273
       grind)
    | exact resolve eq13 eq3273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq3469 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462
  have eq3581 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq431
    | (have j0 := eq431 (τ X0) X1
       grind)
    | exact resolve eq431 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq431
  have eq3594 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3581 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3581
    | (have j0 := eq3581 X0 X1
       grind)
    | exact resolve eq3581 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3581
  have eq3612 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3594 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3594
    | (have j0 := eq3594 X0 X1
       grind)
    | exact resolve eq3594 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594
  have eq4094 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2341 eq59
    | exact resolve eq59 eq2341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq2341
  have eq4879 : ∀ X0 : G, (k X0 y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3469 eq1303
    | exact resolve eq1303 eq3469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303 eq3469
  have eq4928 : ∀ X0 : G, (k X0 y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4879 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4879
  have eq18601 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2813 eq4094
    | exact resolve eq4094 eq2813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2813 eq4094
  have eq18632 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq18601
  have eq18636 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq18632
    | exact resolve eq18632 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18632
  have eq18643 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4928 x
       have i₂ := eq18636
       grind)
    | exact superpose eq18636 eq4928
    | exact resolve eq4928 eq18636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4928
  have eq18645 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93 x y
       have i₂ := eq18636
       grind)
    | exact superpose eq18636 eq93
    | (have j0 := eq93 x y
       grind)
    | exact resolve eq93 eq18636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18636
  have eq18658 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq18645
  have eq18660 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq18643
  have eq18720 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18658
       grind)
    | exact superpose eq18658 eq14
    | exact resolve eq14 eq18658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18658
  have eq361868 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18660 eq18720
    | exact resolve eq18720 eq18660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18660 eq18720
  have eq361931 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq361868
  have eq361942 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq361931
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq361931
    | exact resolve eq361931 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871 eq361931
  have eq362005 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq361942
  have eq362007 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq362005
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq362005
    | exact resolve eq362005 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362005
  have eq362008 : x = (M.op x y) := by grind
  clear eq362007
  have eq362010 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq362008 eq20
    | exact resolve eq20 eq362008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362012 : ∀ X0 : G, y = (M.op y (M.op x (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq362008 eq50
    | exact resolve eq50 eq362008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq362017 : x ≠ x ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq362008 eq74
    | (have r₁ := eq74
       have r₂ := eq362008
       grind)
    | exact resolve eq74 eq362008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq362217 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq362017
  have eq362362 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq362010
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq362010
    | exact resolve eq362010 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq362010
  have eq362366 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq362362 eq26
    | exact resolve eq26 eq362362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq362459 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq362362 eq3073
    | exact resolve eq3073 eq362362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073
  have eq362785 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq362459
       have r₂ := eq27
       grind)
    | exact resolve eq362459 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362459
  have eq363409 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq362217
       grind)
    | exact superpose eq362217 eq71
    | exact resolve eq71 eq362217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362217
  have eq363491 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq362362 eq363409
    | exact resolve eq363409 eq362362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363409
  have eq363532 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq363491
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq363491
    | exact resolve eq363491 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363491
  have eq363706 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq363532 eq93
    | (have j0 := eq93 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq93 eq363532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363532
  have eq363719 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq362366 eq363706
    | exact resolve eq363706 eq362366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363706
  have eq363732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq362366 eq363719
    | exact resolve eq363719 eq362366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363719
  have eq363742 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq363732
       have r₂ := eq27
       grind)
    | exact resolve eq363732 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363732
  have eq363749 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq363742
       grind)
    | exact superpose eq363742 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq363742
       grind)
    | exact resolve eq13 eq363742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363742
  have eq363800 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq363749 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363749
  have eq364008 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq363800 y
       grind)
    | exact superpose eq363800 eq71
    | exact resolve eq71 eq363800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq363800
  have eq364513 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq362362 eq364008
    | exact resolve eq364008 eq362362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362362 eq364008
  have eq364799 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq364513
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq364513
    | exact resolve eq364513 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364513
  have eq364942 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq364799
    | exact resolve eq364799 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq364799
  have eq364985 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq364942
       have r₂ := eq362785
       grind)
    | exact resolve eq364942 eq362785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362785 eq364942
  have eq365019 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq364985 eq51
    | exact resolve eq51 eq364985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq365023 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq364985 eq229
    | exact resolve eq229 eq364985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq364985
  have eq365411 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq365023 eq365019
    | exact resolve eq365019 eq365023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365019 eq365023
  have eq365597 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq365411 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq365411
       grind)
    | exact resolve eq13 eq365411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365648 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq365597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365597
  have eq365952 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq365648 eq87
    | exact resolve eq87 eq365648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq365648
  have eq366429 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq365411 eq365952
    | exact resolve eq365952 eq365411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365952
  have eq366500 : y = (k y y) := by
    first
    | exact superpose eq29 eq366429
    | exact resolve eq366429 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq366429
  have eq366558 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq3612 y X0
       have i₂ := eq366500
       grind)
    | exact superpose eq366500 eq3612
    | (have j0 := eq3612 y X0
       grind)
    | (have r₁ := eq3612 y x
       have r₂ := eq366500
       grind)
    | exact resolve eq3612 eq366500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3612
  have eq366560 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq93 y y
       have i₂ := eq366500
       grind)
    | exact superpose eq366500 eq93
    | (have j0 := eq93 y y
       grind)
    | exact resolve eq93 eq366500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq366500
  have eq366576 : y = (M.op y y) := by grind
  clear eq366560
  have eq366578 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq366558 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366558
  have eq366712 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq362012 y
       have i₂ := eq366576
       grind)
    | exact superpose eq366576 eq362012
    | exact resolve eq362012 eq366576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362012 eq366576
  have eq366769 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq366712
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq366712
    | exact resolve eq366712 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq366712
  have eq366798 : y = (M.op y x) := by
    first
    | exact superpose eq362008 eq366769
    | exact resolve eq366769 eq362008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366769
  have eq367096 : (σ y) ≠ (σ (M.op y (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3381 y
       have i₂ := eq366578 sF0
       grind)
    | exact superpose eq366578 eq3381
    | (have j0 := eq3381 y
       grind)
    | exact resolve eq3381 eq366578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381 eq366578
  have eq367495 : (σ y) ≠ (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq362008 eq367096
    | exact resolve eq367096 eq362008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362008 eq367096
  have eq367777 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq367495
       have i₂ := eq366798
       grind)
    | exact superpose eq366798 eq367495
    | exact resolve eq367495 eq366798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366798 eq367495
  have eq367778 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq367777
  have eq367986 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq367778
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq367778
    | exact resolve eq367778 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq367778
  have eq368298 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op X0 (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq367986 eq14
    | exact resolve eq14 eq367986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375162 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq367986 eq368298
    | exact resolve eq368298 eq367986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367986 eq368298
  have eq375254 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq365411 eq375162
    | exact resolve eq375162 eq365411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365411 eq375162
  have eq375257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq362366 eq375254
    | exact resolve eq375254 eq362366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362366 eq375254
  have eq375259 : False := by grind
  exact eq375259

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation838 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  clear eq18
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
  have eq530 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq643 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq533 x y
       grind)
    | exact superpose eq533 eq16
    | (have j1 := eq533 y x
       grind)
    | exact resolve eq16 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq533 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3182 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq530 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq530
    | exact resolve eq530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq3245 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3182 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3182
    | (have j0 := eq3182 X0 X1
       grind)
    | exact resolve eq3182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3182
  have eq7441 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq643
       have i₂ := eq3245 x y
       grind)
    | exact superpose eq3245 eq643
    | (have j1 := eq3245 (σ y) (σ x)
       grind)
    | (have r₁ := eq643
       have r₂ := eq3245 x y
       grind)
    | (have r₁ := eq643
       have r₂ := eq3245 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq643
       have r₂ := eq3245 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq643 eq3245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3245
  have eq7442 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq7441
  have eq14846 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq654 X1 X0
       have i₂ := eq533 X0 X1
       grind)
    | exact superpose eq533 eq654
    | (have j0 := eq654 X0 X1
       have j1 := eq533 X0 X1
       grind)
    | (have r₁ := eq654 X0 X0
       have r₂ := eq533 X0 X0
       grind)
    | exact resolve eq654 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq14852 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14846 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14846
  have eq14857 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14852 X0 X1
       have j1 := eq654 X0 X1
       grind)
    | (have r₁ := eq14852 X0 X1
       have r₂ := eq654 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq14852 X0 X1
       have r₂ := eq654 (k X1 X0) (k X0 X1)
       grind)
    | (have r₁ := eq14852 X1 X0
       have r₂ := eq654 X0 X1
       grind)
    | exact resolve eq14852 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14852
  have eq15063 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14857 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq14857
    | (have j0 := eq14857 (τ X0) (τ X1)
       grind)
    | exact resolve eq14857 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq14857
  have eq15131 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15063 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq15063
    | (have j0 := eq15063 X0 X1
       grind)
    | exact resolve eq15063 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15063
  have eq15209 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15131 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq15131
    | (have j0 := eq15131 X0 X1
       grind)
    | exact resolve eq15131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15131
  have eq15259 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15209 X1 X0
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq15209
    | (have j0 := eq15209 X0 X1
       grind)
    | (have r₁ := eq15209 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq15209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15209
  have eq15307 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15259 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq15259
    | (have j0 := eq15259 X0 X1
       grind)
    | exact resolve eq15259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15259
  have eq15352 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15307 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15307
    | (have j0 := eq15307 X0 X1
       grind)
    | exact resolve eq15307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15307
  have eq15382 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) ∨ X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15352 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15352
    | (have j0 := eq15352 X0 X1
       grind)
    | exact resolve eq15352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15352
  have eq15400 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15382 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15382
    | (have j0 := eq15382 X0 X1
       grind)
    | exact resolve eq15382 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15382
  have eq21115 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7442
       grind)
    | exact superpose eq7442 eq16
    | exact resolve eq16 eq7442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7442
  have eq21116 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq21115
       have r₂ := eq22 x
       grind)
    | exact resolve eq21115 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21115
  have eq21120 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq21116
       grind)
    | exact superpose eq21116 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21116
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21116
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21116
       grind)
    | exact resolve eq13 eq21116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21116
  have eq21135 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq21120
  have eq21918 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21135
       grind)
    | exact superpose eq21135 eq16
    | exact resolve eq16 eq21135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21135
  have eq21919 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq21918
       have r₂ := eq22 x
       grind)
    | exact resolve eq21918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21918
  have eq21936 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq21919
       grind)
    | exact superpose eq21919 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21919
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq21919
       grind)
    | exact resolve eq13 eq21919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21919
  have eq21956 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq21936
  have eq21957 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq21956
  have eq21970 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq21957
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq21957
    | exact resolve eq21957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21957
  have eq22038 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq643
       have i₂ := eq21970
       grind)
    | exact superpose eq21970 eq643
    | exact resolve eq643 eq21970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq21970
  have eq22053 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq22038
  have eq22054 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq22053
  have eq22058 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq654 y x
       grind)
    | (have r₁ := eq22054
       have r₂ := eq654 y x
       grind)
    | exact resolve eq22054 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq22054
  have eq22075 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq22058
       grind)
    | exact superpose eq22058 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22058
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq22058
       grind)
    | exact resolve eq13 eq22058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22076 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq22058
       grind)
    | exact superpose eq22058 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22058
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq22058
       grind)
    | exact resolve eq13 eq22058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22058
  have eq22093 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq22076
  have eq22094 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq22093
  have eq22095 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq22075
  have eq22096 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq22095
  have eq22108 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22094
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq22094
    | exact resolve eq22094 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22094
  have eq22109 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22096
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22096
    | exact resolve eq22096 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22096
  have eq22185 : (σ (k y x)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22108
       have i₂ := eq22109
       grind)
    | exact superpose eq22109 eq22108
    | exact resolve eq22108 eq22109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22108
  have eq22187 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22109
       grind)
    | exact superpose eq22109 eq16
    | exact resolve eq16 eq22109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22109
  have eq22235 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq22185
  have eq22256 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22235
       grind)
    | exact superpose eq22235 eq10
    | exact resolve eq10 eq22235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22235
  have eq22431 : x = y ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq22256
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22256
    | exact resolve eq22256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22256
  have eq22433 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22431
       grind)
    | exact superpose eq22431 eq16
    | exact resolve eq16 eq22431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22431
  have eq22434 : (σ (k y x)) = (σ (k x y)) := by
    first
    | (have r₁ := eq22433
       have r₂ := eq22 x
       grind)
    | exact resolve eq22433 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22433
  have eq22451 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq22434
       grind)
    | exact superpose eq22434 eq10
    | exact resolve eq10 eq22434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22434
  have eq22628 : (k y x) = (k x y) := by
    first
    | (have i₁ := eq22451
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq22451
    | exact resolve eq22451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22451
  have eq22666 : (k x y) ≠ (k x y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq15400 x y
       have i₂ := eq22628
       grind)
    | exact superpose eq22628 eq15400
    | (have j0 := eq15400 x y
       grind)
    | (have r₁ := eq15400 y x
       have r₂ := eq22628
       grind)
    | (have r₁ := eq15400 x y
       have r₂ := eq22628
       grind)
    | exact resolve eq15400 eq22628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15400 eq22628
  have eq22679 : x = y ∨ (M.op x y) = (M.op y x) := by grind
  clear eq22666
  have eq22686 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22679
       grind)
    | exact superpose eq22679 eq16
    | exact resolve eq16 eq22679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22679
  have eq22687 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq22686
       have r₂ := eq22 x
       grind)
    | exact resolve eq22686 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22686
  have eq22690 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq22687
       grind)
    | exact superpose eq22687 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22687
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22687
       grind)
    | exact resolve eq13 eq22687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22687
  have eq22709 : x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq22690
  have eq22711 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22709
       grind)
    | exact superpose eq22709 eq16
    | exact resolve eq16 eq22709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22709
  have eq22712 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq22711
       have r₂ := eq22 x
       grind)
    | exact resolve eq22711 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22711
  have eq22719 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22187
       have i₂ := eq22712
       grind)
    | exact superpose eq22712 eq22187
    | exact resolve eq22187 eq22712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22187 eq22712
  have eq22757 : (σ x) = (σ y) := by grind
  clear eq22719
  have eq22759 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22757
       grind)
    | exact superpose eq22757 eq16
    | exact resolve eq16 eq22757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22760 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22757
       grind)
    | exact superpose eq22757 eq10
    | exact resolve eq10 eq22757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22757
  have eq22935 : x = y := by
    first
    | (have i₁ := eq22760
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22760
    | exact resolve eq22760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22760
  have eq22936 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq22759
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq22759
    | exact resolve eq22759 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq22759
  have eq22937 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq22936
       have i₂ := eq22935
       grind)
    | exact superpose eq22935 eq22936
    | exact resolve eq22936 eq22935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22935 eq22936
  have eq22938 : False := by grind
  exact eq22938

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36
  have eq58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq85 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq167 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq150
    | (have j0 := eq150 X0 X1
       grind)
    | exact resolve eq150 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq150
  have eq172 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       have j1 := eq85 X1 X0
       grind)
    | (have r₁ := eq167 X1 X0
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq167 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq167 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq167
  have eq184 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq172 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq172
    | exact resolve eq172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq172 (σ X0) X1
       grind)
    | exact superpose eq172 eq15
    | (have j1 := eq172 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq230 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq184 (τ X1) X0
       grind)
    | exact superpose eq184 eq18
    | (have j1 := eq184 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq184
  have eq454 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq230
    | exact resolve eq230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq485 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq454
    | (have j0 := eq454 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq454 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq1256 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq189 x y
       grind)
    | exact superpose eq189 eq16
    | (have j1 := eq189 x y
       grind)
    | exact resolve eq16 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1289 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1256
       have i₂ := eq485 y x
       grind)
    | exact superpose eq485 eq1256
    | (have j1 := eq485 (σ x) (σ y)
       grind)
    | (have r₁ := eq1256
       have r₂ := eq485 y x
       grind)
    | (have r₁ := eq1256
       have r₂ := eq485 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1256
       have r₂ := eq485 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1256 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq1256
  have eq1290 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1289
  have eq1293 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1290
       grind)
    | exact superpose eq1290 eq16
    | exact resolve eq16 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1294 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1293
       have r₂ := eq41 x
       grind)
    | exact resolve eq1293 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1389 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1294
       grind)
    | exact superpose eq1294 eq16
    | exact resolve eq16 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1390 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1294
       grind)
    | exact superpose eq1294 eq10
    | exact resolve eq10 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1433 : x = y := by
    first
    | (have i₁ := eq1390
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1390
    | exact resolve eq1390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1434 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1389
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq1389
    | exact resolve eq1389 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1389
  have eq1435 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1434
       have i₂ := eq1433
       grind)
    | exact superpose eq1433 eq1434
    | exact resolve eq1434 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433 eq1434
  have eq1436 : False := by grind
  exact eq1436

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyy_pxy_pyy_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq57 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq54 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq56 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq109 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq57 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq57
    | (have j0 := eq57 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq57 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq57 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq116 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq119 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq116 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq116 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq116 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq121 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 X1
       have i₂ := eq20 X1
       grind)
    | exact superpose eq20 eq119
    | (have j0 := eq119 X0 X1
       grind)
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq119
  have eq146 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq150 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq146 X0 X1
       have j1 := eq121 X0 X1
       grind)
    | (have r₁ := eq146 X0 X1
       have r₂ := eq121 X0 X1
       grind)
    | (have r₁ := eq146 X1 X1
       have r₂ := eq121 X1 X1
       grind)
    | exact resolve eq146 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq146
  have eq409 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq150 (σ X0) (σ X1)
       grind)
    | exact superpose eq150 eq15
    | exact resolve eq15 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq150 X0 X1
       grind)
    | exact superpose eq150 eq409
    | exact resolve eq409 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq409
  have eq419 : False := by grind
  exact eq419

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_x_pxy_x_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq71 : x ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
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
  have eq72 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq80
    | (have j0 := eq80 (σ x) (σ X0)
       grind)
    | exact resolve eq80 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq44
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq44 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq142 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq163 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq123 eq80
    | (have j0 := eq80 (σ x) (σ y)
       grind)
    | exact resolve eq80 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq190
    | exact resolve eq190 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq194 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq191
       have r₂ := eq27
       grind)
    | exact resolve eq191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq196 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq194
    | exact resolve eq194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq198 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq27
    | exact resolve eq27 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq72
    | (have r₁ := eq72
       have r₂ := eq196
       grind)
    | exact resolve eq72 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq196
  have eq473 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq472
  have eq476 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq473 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq473
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq473
       grind)
    | exact resolve eq13 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq1977 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq476 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq1980 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1977
    | exact resolve eq1977 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq1986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq123 eq1980
    | exact resolve eq1980 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq1980
  have eq1994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1986
  have eq1997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1994
       have r₂ := eq198
       grind)
    | exact resolve eq1994 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq1994
  have eq1998 : x = (M.op x y) := by
    first
    | (have r₁ := eq1997
       have r₂ := eq27
       grind)
    | exact resolve eq1997 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997
  have eq2068 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1998 eq20
    | exact resolve eq20 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2070 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq1998 eq71
    | (have r₁ := eq71
       have r₂ := eq1998
       grind)
    | exact resolve eq71 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2079 : (M.op x x) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq2070
  have eq2089 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2068
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2068
    | exact resolve eq2068 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2092 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2089 eq26
    | exact resolve eq26 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2339 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2079
       grind)
    | exact superpose eq2079 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2079
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2079
       grind)
    | exact resolve eq13 eq2079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq2557 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2089 eq104
    | (have j0 := eq104 X0
       grind)
    | exact resolve eq104 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq2558 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2089 eq2557
    | (have j0 := eq2557 X0
       grind)
    | exact resolve eq2557 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq2673 : (σ (k x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2558 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2558
    | (have j0 := eq2558 y
       grind)
    | exact resolve eq2558 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2558
  have eq2679 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2092 eq2673
    | exact resolve eq2673 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673
  have eq2703 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2679
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq2679
    | exact resolve eq2679 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2679
  have eq2721 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2089 eq2703
    | exact resolve eq2703 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq2730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2092 eq2721
    | exact resolve eq2721 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092 eq2721
  have eq2735 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq2730
       have r₂ := eq27
       grind)
    | exact resolve eq2730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq2744 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq2735 eq163
    | exact resolve eq163 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq2735
  have eq2747 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1998 eq2744
    | exact resolve eq2744 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744
  have eq717102 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2339 X0
       have i₂ := eq2747
       grind)
    | exact superpose eq2747 eq2339
    | (have j0 := eq2339 X0
       grind)
    | exact resolve eq2339 eq2747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339
  have eq717659 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x y) := by
    first
    | (have j0 := eq717102 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717102
  have eq717662 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq717659
       have i₂ := eq2747
       grind)
    | exact superpose eq2747 eq717659
    | exact resolve eq717659 eq2747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747 eq717659
  have eq717672 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq717662
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq717662
    | exact resolve eq717662 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq717662
  have eq717676 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1998 eq717672
    | exact resolve eq717672 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998 eq717672
  have eq717677 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq717676
  have eq717728 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq717677 eq15
    | exact resolve eq15 eq717677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717677
  have eq718343 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq717728
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq717728
    | exact resolve eq717728 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq717728
  have eq718434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2089 eq718343
    | exact resolve eq718343 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089 eq718343
  have eq718467 : False := by grind
  exact eq718467

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_pyy_pxy_pyy_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq41 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq43 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq102 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq344 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq345 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq344 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq350 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq345 X0 X1
       have j1 := eq102 X0 X1
       grind)
    | (have r₁ := eq345 X0 X1
       have r₂ := eq102 X0 X1
       grind)
    | (have r₁ := eq345 X1 X1
       have r₂ := eq102 X1 X1
       grind)
    | exact resolve eq345 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq345
  have eq510 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq350 (σ X0) (σ X1)
       grind)
    | exact superpose eq350 eq15
    | exact resolve eq15 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X1
       have i₂ := eq350 X0 X1
       grind)
    | exact superpose eq350 eq510
    | exact resolve eq510 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq510
  have eq520 : False := by grind
  exact eq520

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pxy_pxy_pxx_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
  have eq318 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq318
  have eq326 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq339 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq326 (σ X0)
       grind)
    | exact superpose eq326 eq15
    | exact resolve eq15 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq326 (τ X0)
       grind)
    | exact superpose eq326 eq32
    | exact resolve eq32 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq345 X0
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq345
    | exact resolve eq345 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq358 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq339 X0
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq339
    | exact resolve eq339 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq339
  have eq404 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq358 X0
       grind)
    | exact superpose eq358 eq13
    | exact resolve eq13 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq411 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq405 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq405
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq416 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq411
  have eq611 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq614 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq637 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq614 X0 X1
       have i₂ := eq358 X0
       grind)
    | exact superpose eq358 eq614
    | (have j0 := eq614 X0 X1
       grind)
    | exact resolve eq614 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq651 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq358 X0
       grind)
    | exact superpose eq358 eq637
    | (have j0 := eq637 X0 X1
       grind)
    | exact resolve eq637 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq637
  have eq4106 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq651 x y
       grind)
    | exact superpose eq651 eq16
    | (have j1 := eq651 x y
       grind)
    | exact resolve eq16 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4219 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq651 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq10242 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq611 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq611
    | exact resolve eq611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq10357 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10242 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10242
    | (have j0 := eq10242 X0 X1
       grind)
    | exact resolve eq10242 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10242
  have eq21753 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4106
       have i₂ := eq10357 y x
       grind)
    | exact superpose eq10357 eq4106
    | (have j1 := eq10357 y x
       grind)
    | (have r₁ := eq4106
       have r₂ := eq10357 y x
       grind)
    | exact resolve eq4106 eq10357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106 eq10357
  have eq21754 : (M.op x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq21753
  have eq29037 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4219 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq4219
    | (have j0 := eq4219 (τ X0) (τ X1)
       grind)
    | exact resolve eq4219 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq29112 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29037 X0 X1
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq29037
    | (have j0 := eq29037 X0 X1
       grind)
    | exact resolve eq29037 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29037
  have eq29152 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29112 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq29112
    | (have j0 := eq29112 X0 X1
       grind)
    | exact resolve eq29112 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29112
  have eq29191 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29152 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq29152
    | (have j0 := eq29152 X0 X1
       grind)
    | exact resolve eq29152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29152
  have eq29230 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29191 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29191
    | (have j0 := eq29191 X0 X1
       grind)
    | exact resolve eq29191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29191
  have eq29253 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29230 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29230
    | (have j0 := eq29230 X0 X1
       grind)
    | exact resolve eq29230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29230
  have eq29275 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29253 X0 X1
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq29253
    | (have j0 := eq29253 X0 X1
       grind)
    | exact resolve eq29253 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29253
  have eq29293 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29275 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq29275
    | (have j0 := eq29275 X0 X1
       grind)
    | exact resolve eq29275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29275
  have eq29309 : ∀ X0 X1 : G, (σ (τ X1)) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29293 X0 X1
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq29293
    | (have j0 := eq29293 X0 X1
       grind)
    | exact resolve eq29293 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq29293
  have eq29320 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29309 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq29309
    | (have j0 := eq29309 X0 X1
       grind)
    | exact resolve eq29309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29309
  have eq29331 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29320 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29320
    | (have j0 := eq29320 X0 X1
       grind)
    | exact resolve eq29320 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29320
  have eq88119 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq21754
       grind)
    | exact superpose eq21754 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21754
       grind)
    | exact resolve eq13 eq21754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21754
  have eq88120 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq88119
  have eq88121 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq88120
  have eq104660 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq404 x (σ y)
       have i₂ := eq88121
       grind)
    | exact superpose eq88121 eq404
    | (have j0 := eq404 x (σ y)
       grind)
    | (have r₁ := eq404 x (σ y)
       have r₂ := eq88121
       grind)
    | exact resolve eq404 eq88121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88121
  have eq104673 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq104660
  have eq104674 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq104673
  have eq104677 : (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq104674
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq104674
    | exact resolve eq104674 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104674
  have eq104688 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4219 x y
       have i₂ := eq104677
       grind)
    | exact superpose eq104677 eq4219
    | (have j0 := eq4219 x y
       grind)
    | (have r₁ := eq4219 x y
       have r₂ := eq104677
       grind)
    | exact resolve eq4219 eq104677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104677
  have eq104796 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq104688
  have eq104797 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq104796
  have eq104801 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq4219 x y
       grind)
    | (have r₁ := eq104797
       have r₂ := eq4219 x y
       grind)
    | exact resolve eq104797 eq4219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4219 eq104797
  have eq104804 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq104801
       grind)
    | exact superpose eq104801 eq16
    | exact resolve eq16 eq104801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104805 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq404 x (σ y)
       have i₂ := eq104801
       grind)
    | exact superpose eq104801 eq404
    | (have j0 := eq404 x (σ y)
       grind)
    | (have r₁ := eq404 x (σ y)
       have r₂ := eq104801
       grind)
    | exact resolve eq404 eq104801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq104801
  have eq104818 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq104805
  have eq104819 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq104818
  have eq104822 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq104819
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq104819
    | exact resolve eq104819 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104819
  have eq106033 : (k x y) = (τ (σ (M.op x x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq104822
       grind)
    | exact superpose eq104822 eq10
    | exact resolve eq10 eq104822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104822
  have eq106329 : (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq106033
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq106033
    | exact resolve eq106033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106033
  have eq106379 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29331 x y
       have i₂ := eq106329
       grind)
    | exact superpose eq106329 eq29331
    | (have j0 := eq29331 x y
       grind)
    | (have r₁ := eq29331 x y
       have r₂ := eq106329
       grind)
    | exact resolve eq29331 eq106329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29331 eq106329
  have eq106408 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq106379
  have eq106409 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq106408
  have eq106453 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq104804
       have i₂ := eq106409
       grind)
    | exact superpose eq106409 eq104804
    | exact resolve eq104804 eq106409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104804 eq106409
  have eq106460 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq106453
  have eq106461 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq106460
  have eq106658 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq106461
       grind)
    | exact superpose eq106461 eq10
    | exact resolve eq10 eq106461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106461
  have eq106942 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq106658
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq106658
    | exact resolve eq106658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106658
  have eq106943 : y = (M.op x x) := by grind
  clear eq106942
  have eq106966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq416 x
       have i₂ := eq106943
       grind)
    | exact superpose eq106943 eq416
    | exact resolve eq416 eq106943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq106943
  have eq107410 : False := by grind
  exact eq107410
