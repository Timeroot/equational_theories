import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 (M.op X0 X0) X0 X2
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq64
    | exact resolve eq64 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq275 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq19
    | exact resolve eq19 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq533 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq744 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq757 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  have eq2720 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq744 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq744
    | (have j0 := eq744 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq744 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2721 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq2746 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq744 X1 X0
       grind)
    | exact superpose eq744 eq15
    | (have j1 := eq744 X1 X0
       grind)
    | exact resolve eq15 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq9979 : ∀ X0 : G, (σ (k (σ (τ (τ X0))) (τ X0))) = (k (σ (k (σ (τ (τ X0))) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq757 (τ X0) (τ (τ X0))
       grind)
    | exact superpose eq757 eq275
    | (have j1 := eq757 (τ X0) (τ (τ X0))
       grind)
    | exact resolve eq275 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq757
  have eq10035 : ∀ X0 : G, (σ (k (σ (τ (τ X0))) (τ X0))) = (k (σ (k (σ (τ (τ X0))) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq9979 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9979
  have eq10038 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = (k (k (σ (σ (τ (τ X0)))) X0) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10035 X0
       have i₂ := eq19 X0 (σ (τ (τ X0)))
       grind)
    | exact superpose eq19 eq10035
    | (have j0 := eq10035 X0
       grind)
    | exact resolve eq10035 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq10035
  have eq10042 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10038 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq10038
    | (have j0 := eq10038 X0
       grind)
    | exact resolve eq10038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10038
  have eq10043 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq10042 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10042
    | (have j0 := eq10042 X0
       grind)
    | exact resolve eq10042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10042
  have eq10613 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) X1) = X1 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (τ (τ X0)) X1
       have i₂ := eq10043 X0
       grind)
    | exact superpose eq10043 eq76
    | (have j1 := eq10043 X0
       grind)
    | exact resolve eq76 eq10043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10676 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq533 (τ (τ X0)) (τ (τ X0)) x
       have i₂ := eq10043 X0
       grind)
    | exact superpose eq10043 eq533
    | (have j1 := eq10043 X0
       grind)
    | exact resolve eq533 eq10043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10043
  have eq10716 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10676 X0 X1
       have i₂ := eq89 (τ (τ X0)) X1
       grind)
    | exact superpose eq89 eq10676
    | (have j0 := eq10676 X0 X1
       grind)
    | exact resolve eq10676 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10676
  have eq11813 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (τ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq10716 eq10613
    | (have j0 := eq10613 X0 X1
       have j1 := eq10716 X0 X1
       grind)
    | exact resolve eq10613 eq10716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10613
  have eq11983 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | exact superpose eq11813 eq10716
    | (have j0 := eq10716 X0 X1
       have j1 := eq11813 X0 X1
       grind)
    | exact resolve eq10716 eq11813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10716 eq11813
  have eq13312 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq11983 (σ X0) X1
       grind)
    | exact superpose eq11983 eq23
    | (have j1 := eq11983 (σ X0) X1
       grind)
    | exact resolve eq23 eq11983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11983
  have eq13360 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13312 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13312
    | (have j0 := eq13312 X0 X1
       grind)
    | exact resolve eq13312 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13312
  have eq13400 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13360 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13360
    | (have j0 := eq13360 X0 X1
       grind)
    | exact resolve eq13360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13360
  have eq13436 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13400 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13400
    | (have j0 := eq13400 X0 X1
       grind)
    | exact resolve eq13400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13400
  have eq13510 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq13436 (σ X0) X1
       grind)
    | exact superpose eq13436 eq23
    | (have j1 := eq13436 (σ X0) X1
       grind)
    | exact resolve eq23 eq13436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13436
  have eq13558 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13510 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13510
    | (have j0 := eq13510 X0 X1
       grind)
    | exact resolve eq13510 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13510
  have eq13598 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13558 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13558
    | (have j0 := eq13558 X0 X1
       grind)
    | exact resolve eq13558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13558
  have eq13634 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13598 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13598
    | (have j0 := eq13598 X0 X1
       grind)
    | exact resolve eq13598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13598
  have eq13708 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq13634 (σ X0) X1
       grind)
    | exact superpose eq13634 eq23
    | (have j1 := eq13634 (σ X0) X1
       grind)
    | exact resolve eq23 eq13634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13634
  have eq13756 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13708 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13708
    | (have j0 := eq13708 X0 X1
       grind)
    | exact resolve eq13708 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13708
  have eq13796 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13756 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13756
    | (have j0 := eq13756 X0 X1
       grind)
    | exact resolve eq13756 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13756
  have eq18748 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq2746
  have eq18764 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18748 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18748
  have eq18779 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq13796 eq18764
    | (have j0 := eq18764 X0
       have j1 := eq13796 X0 (σ X0)
       grind)
    | exact resolve eq18764 eq13796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13796 eq18764
  have eq18804 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18779 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq18779
    | (have j0 := eq18779 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq18779 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18779
  have eq18888 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq18804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18804
  have eq28260 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 (σ X0) (σ X0)
       have i₂ := eq18888 X0
       grind)
    | exact superpose eq18888 eq89
    | (have j1 := eq18888 X0
       grind)
    | exact resolve eq89 eq18888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18888
  have eq31470 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2720 x y
       grind)
    | exact superpose eq2720 eq16
    | (have j1 := eq2720 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2720 x y
       grind)
    | exact resolve eq16 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq31656 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq31470
  have eq61338 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq31656
       grind)
    | exact superpose eq31656 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq31656
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq31656
       grind)
    | exact resolve eq13 eq31656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61358 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ y) (σ x)
       have i₂ := eq31656
       grind)
    | exact superpose eq31656 eq89
    | exact resolve eq89 eq31656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31656
  have eq61450 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq61338
  have eq61451 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq61450
  have eq61512 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq61451
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq61451
    | exact resolve eq61451 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61451
  have eq61529 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq61512
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq61512 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61512
  have eq91974 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq61529
  have eq92183 : (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91974
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq91974
    | exact resolve eq91974 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91974
  have eq92197 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq92183
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq92183 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92183
  have eq92198 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq92197
  have eq92207 : (M.op x y) = (τ (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq92198
       grind)
    | exact superpose eq92198 eq10
    | exact resolve eq10 eq92198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92198
  have eq92367 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92207
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq92207
    | exact resolve eq92207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92207
  have eq92369 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq92367
       grind)
    | exact superpose eq92367 eq9
    | exact resolve eq9 eq92367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92576 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq92369 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq92369
    | exact resolve eq92369 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92369
  have eq93438 : (M.op y x) = (M.op x (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110 x y
       have i₂ := eq92576 x
       grind)
    | exact superpose eq92576 eq110
    | exact resolve eq110 eq92576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq92576
  have eq93752 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq92367 eq93438
    | exact resolve eq93438 eq92367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92367 eq93438
  have eq93753 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq93752
  have eq93843 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) y) X1) X0) X1) = X1 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 x y X1
       have i₂ := eq93753
       grind)
    | exact superpose eq93753 eq65
    | exact resolve eq65 eq93753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq168261 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq61358
       grind)
    | exact superpose eq61358 eq36
    | exact resolve eq36 eq61358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61358
  have eq168582 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq168261
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq168261
    | exact resolve eq168261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168261
  have eq168707 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ x) (σ x)
       have i₂ := eq168582
       grind)
    | exact superpose eq168582 eq89
    | exact resolve eq89 eq168582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168582
  have eq169139 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq168707
       grind)
    | exact superpose eq168707 eq16
    | exact resolve eq16 eq168707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168707
  have eq169368 : (σ y) ≠ (σ y) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq93753 eq169139
    | exact resolve eq169139 eq93753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93753 eq169139
  have eq169369 : y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq169368
  have eq169471 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq169369
       grind)
    | exact superpose eq169369 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq169369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169369
  have eq169472 : y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq169471
  have eq169508 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq169472
       grind)
    | exact superpose eq169472 eq76
    | exact resolve eq76 eq169472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169605 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq533 y y x
       have i₂ := eq169472
       grind)
    | exact superpose eq169472 eq533
    | exact resolve eq533 eq169472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169472
  have eq169787 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq169605 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq169605
    | exact resolve eq169605 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169605
  have eq170962 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq169787 eq169508
    | exact resolve eq169508 eq169787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169508 eq169787
  have eq170986 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq89 y x
       have i₂ := eq170962 X0
       grind)
    | exact superpose eq170962 eq89
    | (have j1 := eq170962 y
       grind)
    | exact resolve eq89 eq170962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170962
  have eq171874 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq170986 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170986
  have eq171875 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq171874
  have eq171982 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq171875
       grind)
    | exact superpose eq171875 eq76
    | exact resolve eq76 eq171875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172008 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2721 y
       have i₂ := eq171875
       grind)
    | exact superpose eq171875 eq2721
    | exact resolve eq2721 eq171875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172079 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq533 y y x
       have i₂ := eq171875
       grind)
    | exact superpose eq171875 eq533
    | exact resolve eq533 eq171875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq171875
  have eq172216 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq172008
  have eq172261 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq172079 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq172079
    | exact resolve eq172079 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172079
  have eq172847 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 (σ y) X0
       have i₂ := eq172216
       grind)
    | exact superpose eq172216 eq76
    | exact resolve eq76 eq172216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq172216
  have eq173529 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq172261 eq171982
    | exact resolve eq171982 eq172261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171982
  have eq173538 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq173529 eq172261
    | exact resolve eq172261 eq173529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172261
  have eq173799 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq173538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173538
  have eq173803 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq173799 eq93843
    | exact resolve eq93843 eq173799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93843
  have eq173903 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq89 x x
       have i₂ := eq173799 X0
       grind)
    | exact superpose eq173799 eq89
    | (have j1 := eq173799 x
       grind)
    | exact resolve eq89 eq173799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq173799
  have eq174092 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq173529 eq173803
    | exact resolve eq173803 eq173529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173529 eq173803
  have eq175679 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq173903 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173903
  have eq175680 : y = (M.op x y) := by grind
  clear eq175679
  have eq175722 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175680
       grind)
    | exact superpose eq175680 eq16
    | exact resolve eq16 eq175680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175680
  have eq177234 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq172847 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172847
  have eq185004 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq174092 eq177234
    | exact resolve eq177234 eq174092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177234
  have eq185252 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq174092 X0 (σ y)
       have i₂ := eq185004 X0
       grind)
    | exact superpose eq185004 eq174092
    | exact resolve eq174092 eq185004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174092 eq185004
  have eq185466 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq185252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185252
  have eq186625 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq175722
       have i₂ := eq185466 (σ x)
       grind)
    | exact superpose eq185466 eq175722
    | (have r₁ := eq175722
       have r₂ := eq185466 (σ x)
       grind)
    | exact resolve eq175722 eq185466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185466
  have eq186668 : y = (M.op x x) := by grind
  clear eq186625
  have eq187616 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq28260 x
       have i₂ := eq186668
       grind)
    | exact superpose eq186668 eq28260
    | (have j0 := eq28260 x
       grind)
    | exact resolve eq28260 eq186668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28260
  have eq187868 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq187616
       have r₂ := eq175722
       grind)
    | exact resolve eq187616 eq175722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187616
  have eq192614 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = y := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq187868
       grind)
    | exact superpose eq187868 eq36
    | exact resolve eq36 eq187868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq187868
  have eq192934 : x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq192614
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq192614
    | exact resolve eq192614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192614
  have eq193032 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq192934
       grind)
    | exact superpose eq192934 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq192934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192934
  have eq193033 : x = (M.op x x) ∨ x = y := by grind
  clear eq193032
  have eq193051 : x = y ∨ x = y := by
    first
    | (have i₁ := eq193033
       have i₂ := eq186668
       grind)
    | exact superpose eq186668 eq193033
    | exact resolve eq193033 eq186668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193033
  have eq193052 : x = y := by grind
  clear eq193051
  have eq193082 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq175722
       have i₂ := eq193052
       grind)
    | exact superpose eq193052 eq175722
    | exact resolve eq175722 eq193052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175722
  have eq193102 : x = (M.op x x) := by
    first
    | (have i₁ := eq186668
       have i₂ := eq193052
       grind)
    | exact superpose eq193052 eq186668
    | exact resolve eq186668 eq193052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186668 eq193052
  have eq193151 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2721 x
       have i₂ := eq193102
       grind)
    | exact superpose eq193102 eq2721
    | exact resolve eq2721 eq193102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721 eq193102
  have eq193359 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq193151
  have eq193431 : False := by grind
  exact eq193431

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_x_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 (M.op X0 X0) X0 X2
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq64
    | exact resolve eq64 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq626 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq2720 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq626 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq626
    | (have j0 := eq626 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq626 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2721 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq626
  have eq15390 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq2721 X0
       grind)
    | exact superpose eq2721 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (σ X0)
       have j1 := eq2721 X0
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have r₂ := eq2721 X0
       grind)
    | exact resolve eq13 eq2721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721
  have eq15464 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq15390 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15390
  have eq15465 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq15464 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15464
  have eq15503 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq15465 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq15465
    | (have j0 := eq15465 X0
       grind)
    | exact resolve eq15465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15465
  have eq15514 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq15503
  have eq15515 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq15514 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15514
  have eq20587 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2720 x y
       grind)
    | exact superpose eq2720 eq16
    | (have j1 := eq2720 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2720 x y
       grind)
    | exact resolve eq16 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq20725 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq20587
  have eq40265 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ y) (σ x)
       have i₂ := eq20725
       grind)
    | exact superpose eq20725 eq89
    | exact resolve eq89 eq20725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20725
  have eq161142 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq40265
       grind)
    | exact superpose eq40265 eq36
    | exact resolve eq36 eq40265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40265
  have eq161465 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq161142
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq161142
    | exact resolve eq161142 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161142
  have eq161496 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq161465
       grind)
    | exact superpose eq161465 eq36
    | exact resolve eq36 eq161465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq161596 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ x) (σ x)
       have i₂ := eq161465
       grind)
    | exact superpose eq161465 eq89
    | exact resolve eq89 eq161465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161465
  have eq161796 : y = (k y x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq161496
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq161496
    | exact resolve eq161496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161496
  have eq161806 : y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq161796
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq161796 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161796
  have eq162888 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq161596
       grind)
    | exact superpose eq161596 eq16
    | exact resolve eq16 eq161596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161596
  have eq163119 : (σ y) ≠ (σ y) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq161806 eq162888
    | exact resolve eq162888 eq161806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161806 eq162888
  have eq163120 : y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq163119
  have eq163231 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq163120
       grind)
    | exact superpose eq163120 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq163120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163120
  have eq163232 : y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq163231
  have eq163270 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq163232
       grind)
    | exact superpose eq163232 eq76
    | exact resolve eq76 eq163232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163367 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq533 y y x
       have i₂ := eq163232
       grind)
    | exact superpose eq163232 eq533
    | exact resolve eq533 eq163232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163232
  have eq163550 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq163367 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq163367
    | exact resolve eq163367 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163367
  have eq164707 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq163550 eq163270
    | exact resolve eq163270 eq163550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163270 eq163550
  have eq164731 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq89 y x
       have i₂ := eq164707 X0
       grind)
    | exact superpose eq164707 eq89
    | (have j1 := eq164707 y
       grind)
    | exact resolve eq89 eq164707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164707
  have eq165542 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq164731 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164731
  have eq165543 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq165542
  have eq165647 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq165543
       grind)
    | exact superpose eq165543 eq76
    | exact resolve eq76 eq165543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq165744 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq533 y y x
       have i₂ := eq165543
       grind)
    | exact superpose eq165543 eq533
    | exact resolve eq533 eq165543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq165543
  have eq165926 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq165744 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq165744
    | exact resolve eq165744 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165744
  have eq167195 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq165926 eq165647
    | exact resolve eq165647 eq165926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165647
  have eq167198 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq167195 eq165926
    | exact resolve eq165926 eq167195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165926
  have eq167250 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15515 x
       have i₂ := eq167195 X0
       grind)
    | exact superpose eq167195 eq15515
    | (have j1 := eq167195 X0
       grind)
    | exact resolve eq15515 eq167195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167195
  have eq167460 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq167198 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167198
  have eq167546 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq89 x x
       have i₂ := eq167460 X0
       grind)
    | exact superpose eq167460 eq89
    | (have j1 := eq167460 x
       grind)
    | exact resolve eq89 eq167460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167460
  have eq169310 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq167546 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167546
  have eq169311 : y = (M.op x y) := by grind
  clear eq169310
  have eq169355 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169311
       grind)
    | exact superpose eq169311 eq16
    | exact resolve eq16 eq169311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169360 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) y) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 x y X1
       have i₂ := eq169311
       grind)
    | exact superpose eq169311 eq64
    | exact resolve eq64 eq169311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq169311
  have eq171497 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j1 := eq167250 X0
       grind)
    | (have r₁ := eq169355
       have r₂ := eq167250 X0
       grind)
    | exact resolve eq169355 eq167250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167250
  have eq176322 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 (σ x) (σ x)
       have i₂ := eq171497 X0
       grind)
    | exact superpose eq171497 eq89
    | (have j1 := eq171497 X0
       grind)
    | exact resolve eq89 eq171497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq171497
  have eq176507 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq176322 X0
       grind)
    | (have r₁ := eq176322 X0
       have r₂ := eq169355
       grind)
    | exact resolve eq176322 eq169355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176322
  have eq176617 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15515 y
       have i₂ := eq176507 y
       grind)
    | exact superpose eq176507 eq15515
    | exact resolve eq15515 eq176507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15515
  have eq176808 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq176507 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq176507 eq77
    | exact resolve eq77 eq176507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq177018 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq176617
  have eq177150 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq176808 X0
       have i₂ := eq176507 y
       grind)
    | exact superpose eq176507 eq176808
    | exact resolve eq176808 eq176507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176808
  have eq177389 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq177150 X0
       have i₂ := eq176507 X0
       grind)
    | exact superpose eq176507 eq177150
    | exact resolve eq177150 eq176507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177150
  have eq177652 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq169360 X0 X1
       have i₂ := eq177389 (M.op x X0)
       grind)
    | exact superpose eq177389 eq169360
    | exact resolve eq169360 eq177389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169360 eq177389
  have eq179072 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177652 X0 X1
       have i₂ := eq176507 X1
       grind)
    | exact superpose eq176507 eq177652
    | exact resolve eq177652 eq176507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176507 eq177652
  have eq179971 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq177018
       grind)
    | exact superpose eq177018 eq9
    | exact resolve eq9 eq177018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177018
  have eq180142 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179971 X0
       have i₂ := eq179072 (σ y) X0
       grind)
    | exact superpose eq179072 eq179971
    | exact resolve eq179971 eq179072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179971
  have eq180344 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq179072 (σ y) X0
       have i₂ := eq180142 X0
       grind)
    | exact superpose eq180142 eq179072
    | exact resolve eq179072 eq180142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179072 eq180142
  have eq180680 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq169355
       have i₂ := eq180344 (σ x)
       grind)
    | exact superpose eq180344 eq169355
    | (have r₁ := eq169355
       have r₂ := eq180344 (σ x)
       grind)
    | exact resolve eq169355 eq180344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169355 eq180344
  have eq181194 : False := by grind
  exact eq181194

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyx_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  clear eq39
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq189 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq186 eq16
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq181 eq184
    | exact resolve eq184 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq184
  have eq562 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq558
       grind)
    | exact superpose eq558 eq16
    | exact resolve eq16 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq568 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq186 eq189
    | exact resolve eq189 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq572 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq568 eq16
    | exact resolve eq16 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq580 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq562 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq562
    | exact resolve eq562 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq586 : (M.op y y) = (k (M.op y y) y) := by
    first
    | (have i₁ := eq180 y
       have i₂ := eq580 y
       grind)
    | exact superpose eq580 eq180
    | exact resolve eq180 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq624 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq625 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq683 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq703 : (σ (M.op y y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq586
       grind)
    | exact superpose eq586 eq40
    | exact resolve eq40 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq722 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq572 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq572
    | exact resolve eq572 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq735 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq722 eq180
    | exact resolve eq180 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq722
  have eq742 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq735 eq152
    | exact resolve eq152 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq735
  have eq803 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq624
       grind)
    | exact superpose eq624 eq40
    | exact resolve eq40 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq803
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq803
    | exact resolve eq803 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq806 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq804
    | exact resolve eq804 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq869 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq192
    | exact resolve eq192 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq888 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq869 X0
       grind)
    | exact superpose eq869 eq16
    | exact resolve eq16 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq869 X0
       grind)
    | exact superpose eq869 eq16
    | exact resolve eq16 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq926 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq888
    | exact resolve eq888 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq888
    | exact resolve eq888 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq934 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq888
    | exact resolve eq888 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq948 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq930 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq930
       grind)
    | exact resolve eq12 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq951 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq948
  have eq1154 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq934 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq934
       grind)
    | exact resolve eq12 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq1154
  have eq1388 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq951 eq41
    | exact resolve eq41 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq951
  have eq1389 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1388
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1388
    | exact resolve eq1388 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1392 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1161 eq90
    | exact resolve eq90 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1161
  have eq1393 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29 eq1392
    | exact resolve eq1392 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq806 eq625
    | exact resolve eq625 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1897 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1888
       have r₂ := eq27
       grind)
    | exact resolve eq1888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1922 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1897 eq869
    | exact resolve eq869 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq1930 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq1922
    | exact resolve eq1922 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922
  have eq1931 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1930
  have eq1965 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq869 y
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq869
    | exact resolve eq869 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq1973 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1965
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1965
    | exact resolve eq1965 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1965
  have eq1974 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1973
  have eq2135 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1974 eq1393
    | exact resolve eq1393 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393 eq1974
  have eq2137 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq2135
    | exact resolve eq2135 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2135
  have eq2233 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2137 eq742
    | exact resolve eq742 eq2137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq2137
  have eq2263 : x = (k x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2233
    | exact resolve eq2233 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233
  have eq2264 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq2263
  have eq2270 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq624
       have i₂ := eq2264
       grind)
    | exact superpose eq2264 eq624
    | exact resolve eq624 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq2272 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2264
       grind)
    | exact superpose eq2264 eq40
    | exact resolve eq40 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2264
  have eq2275 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2270
  have eq2281 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2272
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2272
    | exact resolve eq2272 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq2288 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2281 eq806
    | exact resolve eq806 eq2281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq2281
  have eq2295 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2288
  have eq2325 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq869 y
       have i₂ := eq2275
       grind)
    | exact superpose eq2275 eq869
    | exact resolve eq869 eq2275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2333 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2325
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2325
    | exact resolve eq2325 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325
  have eq2334 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2333
  have eq2424 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq869 y
       have i₂ := eq2295
       grind)
    | exact superpose eq2295 eq869
    | exact resolve eq869 eq2295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2434 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2424
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2424
    | exact resolve eq2424 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq2435 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq2434
  have eq2472 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2435 eq1389
    | exact resolve eq1389 eq2435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435
  have eq2476 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2334 eq2472
    | exact resolve eq2472 eq2334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472
  have eq2973 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2476 eq141
    | exact resolve eq141 eq2476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq2476
  have eq2986 : x = (k x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2973
    | exact resolve eq2973 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2973
  have eq2989 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2334 eq2986
    | exact resolve eq2986 eq2334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq2992 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq684 (M.op x y)
       grind)
    | (have r₁ := eq2989
       have r₂ := eq684 (M.op x y)
       grind)
    | exact resolve eq2989 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq2989
  have eq3017 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2992 eq888
    | exact resolve eq888 eq2992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq3018 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2992 eq889
    | exact resolve eq889 eq2992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq2992
  have eq3023 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3018 x
       have i₂ := eq926 sF0 x
       grind)
    | exact superpose eq926 eq3018
    | exact resolve eq3018 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926 eq3018
  have eq3387 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3023 eq3017
    | exact resolve eq3017 eq3023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017 eq3023
  have eq3415 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387
  have eq3455 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3415 eq174
    | exact resolve eq174 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq3513 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2334 eq3455
    | exact resolve eq3455 eq2334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334 eq3455
  have eq3522 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3415 eq3513
    | exact resolve eq3513 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415 eq3513
  have eq3701 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3522 x
       grind)
    | exact superpose eq3522 eq18
    | (have j1 := eq3522 x
       grind)
    | exact resolve eq18 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3522
  have eq3746 : y = (M.op x y) := by grind
  clear eq3701
  have eq3759 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3746
       grind)
    | exact superpose eq3746 eq24
    | exact resolve eq24 eq3746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3777 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq703
       have i₂ := eq3746
       grind)
    | exact superpose eq3746 eq703
    | exact resolve eq703 eq3746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq3746
  have eq3788 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3759 eq20
    | exact resolve eq20 eq3759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3759
  have eq3827 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3788 eq1389
    | exact resolve eq1389 eq3788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq4962 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3827 eq625
    | exact resolve eq625 eq3827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827
  have eq11719 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4962 eq869
    | exact resolve eq869 eq4962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4962
  have eq11750 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq11719
    | exact resolve eq11719 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11719
  have eq11751 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11750
  have eq11775 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11751 eq3777
    | exact resolve eq3777 eq11751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777 eq11751
  have eq11832 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11775
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11775
    | exact resolve eq11775 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11775
  have eq11901 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11832 eq625
    | exact resolve eq625 eq11832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq11832
  have eq11911 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11901
  have eq11943 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11911 eq869
    | exact resolve eq869 eq11911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq11911
  have eq11974 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11943
    | exact resolve eq11943 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11943
  have eq11975 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11974
  have eq11988 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11975 eq27
    | exact resolve eq27 eq11975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11975
  have eq12016 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11988
       have r₂ := eq3788
       grind)
    | exact resolve eq11988 eq3788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11988
  have eq12020 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq12016 eq27
    | exact resolve eq27 eq12016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq12023 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq12016 eq186
    | exact resolve eq186 eq12016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq12039 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12016 eq934
    | exact resolve eq934 eq12016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq12055 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12039 eq12023
    | exact resolve eq12023 eq12039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12023 eq12039
  have eq12057 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq3788 eq12020
    | exact resolve eq12020 eq3788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788 eq12020
  have eq12133 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12055 eq26
    | exact resolve eq26 eq12055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12055
  have eq12183 : (σ x) = (σ y) := by
    first
    | exact superpose eq12016 eq12133
    | exact resolve eq12133 eq12016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12016 eq12133
  have eq12187 : False := by grind
  exact eq12187

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyy_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  clear eq39
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq192 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : (σ (M.op y y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq180 y
       grind)
    | exact superpose eq180 eq40
    | exact resolve eq40 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq180 sF3
       grind)
    | exact superpose eq180 eq152
    | exact resolve eq152 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq180
  have eq622 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq623 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq672 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq801 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq622
       grind)
    | exact superpose eq622 eq40
    | exact resolve eq40 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq801
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq801
    | exact resolve eq801 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq804 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq802
    | exact resolve eq802 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq858 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq192
    | exact resolve eq192 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq876 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq858 X0
       grind)
    | exact superpose eq858 eq16
    | exact resolve eq16 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq877 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq858 X0
       grind)
    | exact superpose eq858 eq16
    | exact resolve eq16 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq876 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq876
    | exact resolve eq876 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq876
    | exact resolve eq876 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq921 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq876
    | exact resolve eq876 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq935 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq917 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq917
       grind)
    | exact resolve eq12 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq938 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq935
  have eq1127 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq921 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq921
       grind)
    | exact resolve eq12 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1134 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq1127
  have eq1313 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq938 eq41
    | exact resolve eq41 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq938
  have eq1314 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1313
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1313
    | exact resolve eq1313 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1317 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1134 eq90
    | exact resolve eq90 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1134
  have eq1318 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29 eq1317
    | exact resolve eq1317 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq1565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq804 eq623
    | exact resolve eq623 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1572 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1565
       have r₂ := eq27
       grind)
    | exact resolve eq1565 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1594 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1572 eq858
    | exact resolve eq858 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1599 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq1594
    | exact resolve eq1594 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1600 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1599
  have eq1628 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq858 y
       have i₂ := eq1600
       grind)
    | exact superpose eq1600 eq858
    | exact resolve eq858 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1633 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1628
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1628
    | exact resolve eq1628 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1634 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1633
  have eq1663 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1634 eq1318
    | exact resolve eq1318 eq1634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq1634
  have eq1665 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1663
    | exact resolve eq1663 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1663
  have eq1888 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1665 eq251
    | exact resolve eq251 eq1665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq1665
  have eq1913 : x = (k x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1888
    | exact resolve eq1888 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1914 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq1913
  have eq1919 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq622
       have i₂ := eq1914
       grind)
    | exact superpose eq1914 eq622
    | exact resolve eq622 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq1921 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1914
       grind)
    | exact superpose eq1914 eq40
    | exact resolve eq40 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1914
  have eq1924 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1919
  have eq1930 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1921
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1921
    | exact resolve eq1921 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1937 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1930 eq804
    | exact resolve eq804 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq1930
  have eq1944 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1937
  have eq1971 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq858 y
       have i₂ := eq1924
       grind)
    | exact superpose eq1924 eq858
    | exact resolve eq858 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924
  have eq1976 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1971
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1971
    | exact resolve eq1971 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq1977 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1976
  have eq2058 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq858 y
       have i₂ := eq1944
       grind)
    | exact superpose eq1944 eq858
    | exact resolve eq858 eq1944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq2064 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2058
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2058
    | exact resolve eq2058 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq2065 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq2064
  have eq2099 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2065 eq1314
    | exact resolve eq1314 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065
  have eq2103 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1977 eq2099
    | exact resolve eq2099 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099
  have eq2255 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2103 eq141
    | exact resolve eq141 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq2103
  have eq2266 : x = (k x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2255
    | exact resolve eq2255 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2255
  have eq2269 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1977 eq2266
    | exact resolve eq2266 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq2272 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq673 (M.op x y)
       grind)
    | (have r₁ := eq2269
       have r₂ := eq673 (M.op x y)
       grind)
    | exact resolve eq2269 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq2269
  have eq2289 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2272 eq877
    | exact resolve eq877 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq2290 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2272 eq876
    | exact resolve eq876 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq2272
  have eq2295 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2289 x
       have i₂ := eq913 sF0 x
       grind)
    | exact superpose eq913 eq2289
    | exact resolve eq2289 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq2289
  have eq2935 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2295 eq2290
    | exact resolve eq2290 eq2295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290 eq2295
  have eq2962 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2935 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935
  have eq3001 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2962 eq174
    | exact resolve eq174 eq2962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq3048 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1977 eq3001
    | exact resolve eq3001 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977 eq3001
  have eq3055 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2962 eq3048
    | exact resolve eq3048 eq2962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962 eq3048
  have eq3224 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3055 x
       grind)
    | exact superpose eq3055 eq18
    | (have j1 := eq3055 x
       grind)
    | exact resolve eq18 eq3055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3055
  have eq3268 : y = (M.op x y) := by grind
  clear eq3224
  have eq3281 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3268
       grind)
    | exact superpose eq3268 eq24
    | exact resolve eq24 eq3268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3290 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq198
       have i₂ := eq3268
       grind)
    | exact superpose eq3268 eq198
    | exact resolve eq198 eq3268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq3268
  have eq3307 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3281 eq20
    | exact resolve eq20 eq3281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3281
  have eq3346 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3307 eq1314
    | exact resolve eq1314 eq3307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq4396 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3346 eq623
    | exact resolve eq623 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq10939 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4396 eq858
    | exact resolve eq858 eq4396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396
  have eq10965 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq10939
    | exact resolve eq10939 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10939
  have eq10966 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10965
  have eq10987 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10966 eq3290
    | exact resolve eq3290 eq10966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290 eq10966
  have eq11037 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10987
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10987
    | exact resolve eq10987 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10987
  have eq11102 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11037 eq623
    | exact resolve eq623 eq11037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq11037
  have eq11112 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11102
  have eq11144 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11112 eq858
    | exact resolve eq858 eq11112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq11112
  have eq11170 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11144
    | exact resolve eq11144 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11144
  have eq11171 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11170
  have eq11316 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11171 eq27
    | exact resolve eq27 eq11171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11171
  have eq11342 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11316
       have r₂ := eq3307
       grind)
    | exact resolve eq11316 eq3307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11316
  have eq11346 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq11342 eq27
    | exact resolve eq27 eq11342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq11349 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq11342 eq186
    | exact resolve eq186 eq11342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq11364 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11342 eq921
    | exact resolve eq921 eq11342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq11379 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11364 eq11349
    | exact resolve eq11349 eq11364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11349 eq11364
  have eq11381 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq3307 eq11346
    | exact resolve eq11346 eq3307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3307 eq11346
  have eq11446 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11379 eq26
    | exact resolve eq26 eq11379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11379
  have eq11494 : (σ x) = (σ y) := by
    first
    | exact superpose eq11342 eq11446
    | exact resolve eq11446 eq11342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11342 eq11446
  have eq11498 : False := by grind
  exact eq11498

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op (M.op X1 X0) (M.op X1 X2))) = X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op (M.op X1 X0) (M.op X1 X2))) = X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq72 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq89
    | exact resolve eq89 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq114 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq2439 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq77
    | (have j0 := eq77 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq77 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3577 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq67 X0 X1 X2
       grind)
    | exact superpose eq67 eq114
    | (have j1 := eq67 X0 X1 X2
       grind)
    | exact resolve eq114 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq114
  have eq3593 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3577 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3577
  have eq3702 : ∀ X0 X1 : G, (k X1 (M.op (M.op (M.op X0 X0) X1) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3593 X1 (M.op X0 X0) X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq3593
    | exact resolve eq3593 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq3593
  have eq3812 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3702 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq3702
    | exact resolve eq3702 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3702
  have eq3945 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (M.op X0 X1) X0
       have i₂ := eq3812 X0 X1
       grind)
    | exact superpose eq3812 eq77
    | (have j0 := eq77 (M.op X0 X1) X0
       grind)
    | exact resolve eq77 eq3812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3947 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) X1) X0
       have i₂ := eq3812 (σ X0) X1
       grind)
    | exact superpose eq3812 eq23
    | exact resolve eq23 eq3812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq3956 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3945 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3945
  have eq4865 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (M.op X0 X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ (M.op (σ X0) X1)) X0
       have i₂ := eq3947 X0 X1
       grind)
    | exact superpose eq3947 eq14
    | (have j0 := eq14 (τ (M.op (σ X0) X1)) X0
       grind)
    | exact resolve eq14 eq3947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3947
  have eq4874 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (M.op X0 X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4865 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4865
  have eq20472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2439 x y
       grind)
    | exact superpose eq2439 eq16
    | (have j1 := eq2439 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2439 x y
       grind)
    | exact resolve eq16 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq20704 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq20472
  have eq177195 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20704
       grind)
    | exact superpose eq20704 eq16
    | exact resolve eq16 eq20704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177211 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq20704
       grind)
    | exact superpose eq20704 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20704
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20704
       grind)
    | exact resolve eq13 eq20704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20704
  have eq177451 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq177211
  have eq177452 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq177451
  have eq177458 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq177452
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq177452
    | exact resolve eq177452 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177452
  have eq177469 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq177458
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq177458 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177458
  have eq177479 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq177469
       have r₂ := eq177195
       grind)
    | exact resolve eq177469 eq177195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177195 eq177469
  have eq177505 : (τ (σ y)) = (M.op x (τ (σ y))) ∨ (M.op x x) = (τ (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4874 x (σ x)
       have i₂ := eq177479
       grind)
    | exact superpose eq177479 eq4874
    | exact resolve eq4874 eq177479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4874 eq177479
  have eq177967 : y = (M.op x y) ∨ (M.op x x) = (τ (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq177505
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq177505
    | exact resolve eq177505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177505
  have eq177968 : y = (M.op x y) ∨ (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by grind
  clear eq177967
  have eq178012 : y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq177968
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq177968
    | exact resolve eq177968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177968
  have eq178013 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq178012
  have eq178024 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq178013
  have eq178160 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3956 x y
       have i₂ := eq178024
       grind)
    | exact superpose eq178024 eq3956
    | exact resolve eq3956 eq178024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq189637 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq178160
       grind)
    | exact superpose eq178160 eq16
    | exact resolve eq16 eq178160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178160
  have eq189915 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq178024 eq189637
    | exact resolve eq189637 eq178024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189637
  have eq189916 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq189915
  have eq190138 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105 (σ x) (σ x)
       have i₂ := eq189916
       grind)
    | exact superpose eq189916 eq105
    | exact resolve eq105 eq189916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189916
  have eq197732 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq190138
       grind)
    | exact superpose eq190138 eq16
    | exact resolve eq16 eq190138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190138
  have eq198058 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq178024 eq197732
    | exact resolve eq197732 eq178024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178024 eq197732
  have eq198059 : y = (M.op x x) := by grind
  clear eq198058
  have eq198279 : y = (M.op x y) := by
    first
    | (have i₁ := eq105 x x
       have i₂ := eq198059
       grind)
    | exact superpose eq198059 eq105
    | exact resolve eq105 eq198059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198400 : y = (k y x) := by
    first
    | (have i₁ := eq3812 x x
       have i₂ := eq198059
       grind)
    | exact superpose eq198059 eq3812
    | exact resolve eq3812 eq198059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812 eq198059
  have eq198554 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq198279
       grind)
    | exact superpose eq198279 eq16
    | exact resolve eq16 eq198279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198279
  have eq198869 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq77 y x
       have i₂ := eq198400
       grind)
    | exact superpose eq198400 eq77
    | (have j0 := eq77 y x
       grind)
    | exact resolve eq77 eq198400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq198400
  have eq198872 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq198869
  have eq198874 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq198872
       have r₂ := eq198554
       grind)
    | exact resolve eq198872 eq198554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198872
  have eq199094 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq105 (σ x) (σ x)
       have i₂ := eq198874
       grind)
    | exact superpose eq198874 eq105
    | exact resolve eq105 eq198874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq198874
  have eq199357 : False := by grind
  exact eq199357

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq380 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq388 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq14
    | exact resolve eq14 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq696 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq75 X0 X0
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq711 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq696 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq713 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq711 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq711 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq711 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq711 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq722 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq713
    | (have j0 := eq713 X0 X1
       grind)
    | exact resolve eq713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq872 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq388
    | exact resolve eq388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq388
    | exact resolve eq388 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq876 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq388
    | exact resolve eq388 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq388
  have eq8216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8216
    | exact resolve eq8216 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8216
  have eq8228 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8217
       have r₂ := eq28
       grind)
    | exact resolve eq8217 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8217
  have eq8230 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8228
    | exact resolve eq8228 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8228
  have eq8250 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq8230
  have eq8272 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8250
    | exact resolve eq8250 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8250
  have eq10042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8272 eq97
    | exact resolve eq97 eq8272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8272
  have eq10052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10042
  have eq10055 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10052
       have r₂ := eq28
       grind)
    | exact resolve eq10052 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10052
  have eq10076 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10055
  have eq10110 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10076
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10076
    | exact resolve eq10076 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10076
  have eq10694 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq10110
       grind)
    | exact superpose eq10110 eq72
    | exact resolve eq72 eq10110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq10110
  have eq10708 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10694
    | exact resolve eq10694 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10694
  have eq10857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10708 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10857
    | exact resolve eq10857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10857
  have eq10871 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10860
       have r₂ := eq28
       grind)
    | exact resolve eq10860 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10860
  have eq10873 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10871
    | exact resolve eq10871 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10871
  have eq10874 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10873
  have eq10899 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10874
  have eq10941 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq10899
    | exact resolve eq10899 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10899
  have eq11033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10941 eq10708
    | exact resolve eq10708 eq10941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10708 eq10941
  have eq11035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11033
  have eq11041 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11035
       have r₂ := eq28
       grind)
    | exact resolve eq11035 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11035
  have eq11616 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11041 eq216
    | exact resolve eq216 eq11041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq11637 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11041 eq876
    | exact resolve eq876 eq11041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12489 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11637 eq11616
    | exact resolve eq11616 eq11637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11616 eq11637
  have eq12537 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12489
  have eq12541 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12537
    | exact resolve eq12537 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12537
  have eq12544 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12541 eq28
    | exact resolve eq28 eq12541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12576 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12541 eq11041
    | exact resolve eq11041 eq12541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11041
  have eq12579 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq12576
  have eq13286 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12579 eq27
    | exact resolve eq27 eq12579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13287 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12579 eq30
    | exact resolve eq30 eq12579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12579
  have eq13443 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq13287
    | exact resolve eq13287 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13287
  have eq14673 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13286
  have eq14723 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq876 eq14673
    | exact resolve eq14673 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq14673
  have eq16311 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12541 eq14723
    | exact resolve eq14723 eq12541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12541 eq14723
  have eq16329 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq16311
  have eq17472 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16329 eq97
    | exact resolve eq97 eq16329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq16329
  have eq17495 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq17472
  have eq17509 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17495
       have r₂ := eq12544
       grind)
    | exact resolve eq17495 eq12544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12544 eq17495
  have eq17656 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq872 x x
       have i₂ := eq17509
       grind)
    | exact superpose eq17509 eq872
    | exact resolve eq872 eq17509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq17509
  have eq17659 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17656
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17656
    | exact resolve eq17656 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17656
  have eq17760 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq17659
  have eq17762 : x = (M.op x y) := by
    first
    | (have r₁ := eq17760
       have r₂ := eq13443
       grind)
    | exact resolve eq17760 eq13443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13443 eq17760
  have eq17818 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17762 eq21
    | exact resolve eq21 eq17762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq17895 : x = (M.op x x) := by
    first
    | exact superpose eq17762 eq874
    | exact resolve eq874 eq17762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq17961 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17818
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17818
    | exact resolve eq17818 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17818
  have eq17986 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq17961 eq27
    | exact resolve eq27 eq17961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq18145 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq17895
       grind)
    | exact superpose eq17895 eq51
    | exact resolve eq51 eq17895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq18165 : (k x x) = (M.op x x) := by grind
  have eq18216 : x = (k x x) := by
    first
    | (have i₁ := eq18165
       have i₂ := eq17895
       grind)
    | exact superpose eq17895 eq18165
    | exact resolve eq18165 eq17895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18165
  have eq18234 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq17762 eq18145
    | exact resolve eq18145 eq17762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18145
  have eq18251 : y = (M.op x y) := by
    first
    | (have i₁ := eq18234
       have i₂ := eq17895
       grind)
    | exact superpose eq17895 eq18234
    | exact resolve eq18234 eq17895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17895 eq18234
  have eq18258 : y = (M.op x y) := by
    first
    | (have i₁ := eq18251
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18251
    | exact resolve eq18251 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq18251
  have eq18262 : x = y := by
    first
    | exact superpose eq17762 eq18258
    | exact resolve eq18258 eq17762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17762 eq18258
  have eq18265 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq18262
       grind)
    | exact superpose eq18262 eq25
    | exact resolve eq25 eq18262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18262
  have eq18402 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18265
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18265
    | exact resolve eq18265 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18265
  have eq18464 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq17961 eq18402
    | exact resolve eq18402 eq17961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18402
  have eq19478 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq18464 eq17986
    | exact resolve eq17986 eq18464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17986 eq18464
  have eq20631 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq722 x x
       have i₂ := eq18216
       grind)
    | exact superpose eq18216 eq722
    | (have j0 := eq722 x x
       grind)
    | exact resolve eq722 eq18216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq18216
  have eq20632 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq20631
  have eq20633 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq20632
  have eq20647 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20633
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20633
    | exact resolve eq20633 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20633
  have eq20663 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17961 eq20647
    | exact resolve eq20647 eq17961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17961 eq20647
  have eq20744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19478 eq20663
    | exact resolve eq20663 eq19478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19478 eq20663
  have eq20745 : False := by grind
  exact eq20745

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
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
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq515 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq523 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq515 X0
       grind)
    | exact superpose eq515 eq14
    | exact resolve eq14 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq706 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq872 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq523
    | exact resolve eq523 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq523
    | exact resolve eq523 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq876 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq523
    | exact resolve eq523 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq523
  have eq9242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9242
    | exact resolve eq9242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9242
  have eq9254 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq9243
       have r₂ := eq28
       grind)
    | exact resolve eq9243 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9243
  have eq9256 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9254
    | exact resolve eq9254 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9254
  have eq9276 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9256
  have eq9298 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9276
    | exact resolve eq9276 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9276
  have eq11148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9298 eq113
    | exact resolve eq113 eq9298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9298
  have eq11159 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11148
  have eq11162 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11159
       have r₂ := eq28
       grind)
    | exact resolve eq11159 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11159
  have eq11183 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11162
  have eq11219 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11183
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11183
    | exact resolve eq11183 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11183
  have eq11572 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11219
       grind)
    | exact superpose eq11219 eq72
    | exact resolve eq72 eq11219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq11219
  have eq11588 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11572
    | exact resolve eq11572 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11572
  have eq11741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11588 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11741
    | exact resolve eq11741 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11741
  have eq11755 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11744
       have r₂ := eq28
       grind)
    | exact resolve eq11744 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11744
  have eq11757 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11755
    | exact resolve eq11755 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11755
  have eq11758 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11757
  have eq11783 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11758
  have eq11825 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11783
    | exact resolve eq11783 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11783
  have eq12489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11825 eq11588
    | exact resolve eq11588 eq11825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11588 eq11825
  have eq12493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12489
  have eq12499 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12493
       have r₂ := eq28
       grind)
    | exact resolve eq12493 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12493
  have eq12641 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12499 eq216
    | exact resolve eq216 eq12499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq12662 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12499 eq876
    | exact resolve eq876 eq12499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12843 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12662 eq12641
    | exact resolve eq12641 eq12662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12641 eq12662
  have eq12891 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12843
  have eq12894 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12891
    | exact resolve eq12891 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12891
  have eq12897 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12894 eq28
    | exact resolve eq28 eq12894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12930 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12894 eq12499
    | exact resolve eq12499 eq12894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12499
  have eq12933 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq12930
  have eq12947 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12933 eq27
    | exact resolve eq27 eq12933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12948 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12933 eq30
    | exact resolve eq30 eq12933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12933
  have eq13112 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq12948
    | exact resolve eq12948 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12948
  have eq13501 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12947
  have eq13551 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq876 eq13501
    | exact resolve eq13501 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq13501
  have eq14444 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12894 eq13551
    | exact resolve eq13551 eq12894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12894 eq13551
  have eq14458 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq14444
  have eq14695 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14458 eq113
    | exact resolve eq113 eq14458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq14458
  have eq14713 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq14695
  have eq14728 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14713
       have r₂ := eq12897
       grind)
    | exact resolve eq14713 eq12897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12897 eq14713
  have eq14832 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq872 x x
       have i₂ := eq14728
       grind)
    | exact superpose eq14728 eq872
    | exact resolve eq872 eq14728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq14728
  have eq14835 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14832
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14832
    | exact resolve eq14832 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14832
  have eq15812 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq14835
  have eq15814 : x = (M.op x y) := by
    first
    | (have r₁ := eq15812
       have r₂ := eq13112
       grind)
    | exact resolve eq15812 eq13112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13112 eq15812
  have eq15870 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15814 eq21
    | exact resolve eq21 eq15814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq15947 : x = (M.op x x) := by
    first
    | exact superpose eq15814 eq874
    | exact resolve eq874 eq15814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq16013 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15870
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15870
    | exact resolve eq15870 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15870
  have eq16789 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16013 eq27
    | exact resolve eq27 eq16013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq16950 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq15947
       grind)
    | exact superpose eq15947 eq51
    | exact resolve eq51 eq15947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq16970 : (k x x) = (M.op x x) := by grind
  have eq17021 : x = (k x x) := by
    first
    | (have i₁ := eq16970
       have i₂ := eq15947
       grind)
    | exact superpose eq15947 eq16970
    | exact resolve eq16970 eq15947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16970
  have eq17039 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq15814 eq16950
    | exact resolve eq16950 eq15814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16950
  have eq17056 : y = (M.op x y) := by
    first
    | (have i₁ := eq17039
       have i₂ := eq15947
       grind)
    | exact superpose eq15947 eq17039
    | exact resolve eq17039 eq15947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15947 eq17039
  have eq17063 : y = (M.op x y) := by
    first
    | (have i₁ := eq17056
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17056
    | exact resolve eq17056 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17056
  have eq17066 : x = y := by
    first
    | exact superpose eq15814 eq17063
    | exact resolve eq17063 eq15814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15814 eq17063
  have eq17069 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17066
       grind)
    | exact superpose eq17066 eq25
    | exact resolve eq25 eq17066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17066
  have eq17208 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17069
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17069
    | exact resolve eq17069 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17069
  have eq17270 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16013 eq17208
    | exact resolve eq17208 eq16013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17208
  have eq18729 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17270 eq16789
    | exact resolve eq16789 eq17270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16789 eq17270
  have eq20934 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq706 x x
       have i₂ := eq17021
       grind)
    | exact superpose eq17021 eq706
    | (have j0 := eq706 x x
       grind)
    | exact resolve eq706 eq17021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq17021
  have eq20935 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq20934
  have eq20936 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq20935
  have eq20948 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20936
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20936
    | exact resolve eq20936 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20936
  have eq20963 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16013 eq20948
    | exact resolve eq20948 eq16013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16013 eq20948
  have eq22728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18729 eq20963
    | exact resolve eq20963 eq18729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18729 eq20963
  have eq22729 : False := by grind
  exact eq22729

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq37 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq43 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq94 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq94 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq94
    | exact resolve eq94 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 X1 (M.op X0 X0) X0 X2
       have i₂ := eq128 X0
       grind)
    | exact superpose eq128 eq94
    | exact resolve eq94 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq134 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq128 X0
       grind)
    | exact superpose eq128 eq9
    | exact resolve eq9 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq128 X0
       grind)
    | exact superpose eq128 eq9
    | exact resolve eq9 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq134
    | exact resolve eq134 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq135 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq135
    | exact resolve eq135 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq361 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq668 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq132 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq132
    | exact resolve eq132 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq3012 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq361
    | (have j0 := eq361 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq361 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3013 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq361
  have eq28716 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3012 x y
       grind)
    | exact superpose eq3012 eq16
    | (have j1 := eq3012 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3012 x y
       grind)
    | exact resolve eq16 eq3012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28722 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq128 (σ X0)
       have i₂ := eq3012 X0 X0
       grind)
    | exact superpose eq3012 eq128
    | (have j1 := eq3012 X0 X0
       grind)
    | exact resolve eq128 eq3012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3012
  have eq28867 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28722 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28722
  have eq28870 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq28716
  have eq50828 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq28870
       grind)
    | exact superpose eq28870 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq28870
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq28870
       grind)
    | exact resolve eq13 eq28870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50848 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq147 (σ y) (σ x)
       have i₂ := eq28870
       grind)
    | exact superpose eq28870 eq147
    | exact resolve eq147 eq28870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28870
  have eq50941 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq50828
  have eq50942 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq50941
  have eq51001 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50942
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq50942
    | exact resolve eq50942 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50942
  have eq51018 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq51001
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq51001 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51001
  have eq201890 : (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq51018
  have eq202209 : (σ y) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq201890
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq201890
    | exact resolve eq201890 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201890
  have eq202226 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq202209
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq202209 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202209
  have eq202227 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq202226
  have eq202239 : (M.op x y) = (τ (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq202227
       grind)
    | exact superpose eq202227 eq10
    | exact resolve eq10 eq202227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202227
  have eq202431 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq202239
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq202239
    | exact resolve eq202239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202239
  have eq202432 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq202431
       grind)
    | exact superpose eq202431 eq9
    | exact resolve eq9 eq202431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202743 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq202432 X0
       have i₂ := eq147 y X0
       grind)
    | exact superpose eq147 eq202432
    | exact resolve eq202432 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202432
  have eq203987 : (M.op y x) = (M.op x (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq174 x y
       have i₂ := eq202743 x
       grind)
    | exact superpose eq202743 eq174
    | exact resolve eq174 eq202743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq202743
  have eq204417 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq202431 eq203987
    | exact resolve eq203987 eq202431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202431 eq203987
  have eq204418 : y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq204417
  have eq204526 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) y) X1) X0) X1) = X1 ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 x y X1
       have i₂ := eq204418
       grind)
    | exact superpose eq204418 eq95
    | exact resolve eq95 eq204418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq292953 : y = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq50848
       grind)
    | exact superpose eq50848 eq43
    | exact resolve eq43 eq50848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50848
  have eq293395 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq292953
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq292953
    | exact resolve eq292953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292953
  have eq293470 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq128 (σ y)
       have i₂ := eq293395
       grind)
    | exact superpose eq293395 eq128
    | exact resolve eq128 eq293395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293395
  have eq293918 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq293470
       grind)
    | exact superpose eq293470 eq16
    | exact resolve eq16 eq293470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293470
  have eq294197 : (σ y) ≠ (σ y) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq204418 eq293918
    | exact resolve eq293918 eq204418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204418 eq293918
  have eq294198 : y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq294197
  have eq294279 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq294198
       grind)
    | exact superpose eq294198 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq294198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294198
  have eq294280 : y = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq294279
  have eq294342 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq134 y X0
       have i₂ := eq294280
       grind)
    | exact superpose eq294280 eq134
    | exact resolve eq134 eq294280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294462 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq668 y y x
       have i₂ := eq294280
       grind)
    | exact superpose eq294280 eq668
    | exact resolve eq668 eq294280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294280
  have eq294726 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq294462 X0
       have i₂ := eq147 y X0
       grind)
    | exact superpose eq147 eq294462
    | exact resolve eq294462 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294462
  have eq297294 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq294726 eq294342
    | exact resolve eq294342 eq294726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294342
  have eq297295 : ∀ X0 : G, y = (M.op y x) ∨ y = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq297294 eq294726
    | exact resolve eq294726 eq297294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294726
  have eq297321 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq147 y x
       have i₂ := eq297294 X0
       grind)
    | exact superpose eq297294 eq147
    | (have j1 := eq297294 y
       grind)
    | exact resolve eq147 eq297294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297294
  have eq298496 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq297321 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297321
  have eq298498 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq298496
  have eq298640 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq134 y X0
       have i₂ := eq298498
       grind)
    | exact superpose eq298498 eq134
    | exact resolve eq134 eq298498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298667 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3013 y
       have i₂ := eq298498
       grind)
    | exact superpose eq298498 eq3013
    | exact resolve eq3013 eq298498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298760 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq668 y y x
       have i₂ := eq298498
       grind)
    | exact superpose eq298498 eq668
    | exact resolve eq668 eq298498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq298961 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq298498
  have eq298962 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq298667
  have eq299024 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq298760 X0
       have i₂ := eq147 y X0
       grind)
    | exact superpose eq147 eq298760
    | exact resolve eq298760 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq298760
  have eq299726 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq134 (σ y) X0
       have i₂ := eq298962
       grind)
    | exact superpose eq298962 eq134
    | exact resolve eq134 eq298962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq298962
  have eq300697 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq299024 eq298640
    | exact resolve eq298640 eq299024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298640 eq299024
  have eq300707 : ∀ X0 : G, x = y ∨ y = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq300697 eq297295
    | (have j0 := eq297295 X0
       grind)
    | exact resolve eq297295 eq300697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297295
  have eq301072 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq300707 X0
       grind)
    | (have r₁ := eq300707 X0
       have r₂ := eq298961
       grind)
    | exact resolve eq300707 eq298961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298961 eq300707
  have eq301080 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq301072 eq204526
    | exact resolve eq204526 eq301072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204526
  have eq302885 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq300697 eq301080
    | exact resolve eq301080 eq300697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300697 eq301080
  have eq304511 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq299726 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299726
  have eq330519 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq302885 eq304511
    | exact resolve eq304511 eq302885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304511
  have eq330886 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq302885 X0 (σ y)
       have i₂ := eq330519 X0
       grind)
    | exact superpose eq330519 eq302885
    | exact resolve eq302885 eq330519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302885 eq330519
  have eq331155 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq330886 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330886
  have eq331432 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq331155 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331155
  have eq332706 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq331432 (σ x)
       grind)
    | exact superpose eq331432 eq16
    | exact resolve eq16 eq331432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331432
  have eq332820 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq301072 eq332706
    | exact resolve eq332706 eq301072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301072 eq332706
  have eq332821 : x = (M.op y y) := by grind
  clear eq332820
  have eq333831 : y = (M.op x y) := by
    first
    | (have i₁ := eq128 y
       have i₂ := eq332821
       grind)
    | exact superpose eq332821 eq128
    | exact resolve eq128 eq332821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq333893 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq28867 y
       have i₂ := eq332821
       grind)
    | exact superpose eq332821 eq28867
    | (have j0 := eq28867 y
       grind)
    | exact resolve eq28867 eq332821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28867
  have eq335751 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq333831
       grind)
    | exact superpose eq333831 eq16
    | exact resolve eq16 eq333831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333831
  have eq355101 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq335751
       have r₂ := eq333893
       grind)
    | exact resolve eq335751 eq333893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333893
  have eq355105 : y = (k (τ (σ y)) y) ∨ x = y := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq355101
       grind)
    | exact superpose eq355101 eq43
    | exact resolve eq43 eq355101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq355101
  have eq355597 : y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq355105
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq355105
    | exact resolve eq355105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355105
  have eq355721 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq355597
       grind)
    | exact superpose eq355597 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq355597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355597
  have eq355722 : y = (M.op y y) ∨ x = y := by grind
  clear eq355721
  have eq355738 : x = y ∨ x = y := by
    first
    | (have i₁ := eq355722
       have i₂ := eq332821
       grind)
    | exact superpose eq332821 eq355722
    | exact resolve eq355722 eq332821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355722
  have eq355739 : x = y := by grind
  clear eq355738
  have eq355831 : x = (M.op x x) := by
    first
    | (have i₁ := eq332821
       have i₂ := eq355739
       grind)
    | exact superpose eq355739 eq332821
    | exact resolve eq332821 eq355739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332821
  have eq355851 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq335751
       have i₂ := eq355739
       grind)
    | exact superpose eq355739 eq335751
    | exact resolve eq335751 eq355739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335751 eq355739
  have eq355901 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3013 x
       have i₂ := eq355831
       grind)
    | exact superpose eq355831 eq3013
    | exact resolve eq3013 eq355831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3013 eq355831
  have eq356230 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq355901
  have eq356340 : False := by grind
  exact eq356340
