import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_y_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq328 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq769 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X0) (σ X1)
       have i₂ := eq331 X0 X1
       grind)
    | exact superpose eq331 eq64
    | (have j1 := eq331 X0 X1
       grind)
    | exact resolve eq64 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op (σ (k X0 X1)) (σ X0)) X2) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X1) X2
       have i₂ := eq331 X0 X1
       grind)
    | exact superpose eq331 eq9
    | (have j1 := eq331 X0 X1
       grind)
    | exact resolve eq9 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq331
  have eq788 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq795 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq788 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq788
    | (have j0 := eq788 X0
       grind)
    | exact resolve eq788 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq7672 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq328 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq328
    | exact resolve eq328 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq7740 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7672 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7672
    | (have j0 := eq7672 X0 X1
       grind)
    | exact resolve eq7672 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7672
  have eq29709 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq769 (τ X1) (τ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq769
    | (have j0 := eq769 (τ X0) (τ X1)
       grind)
    | exact resolve eq769 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq29833 : ∀ X0 X1 : G, (k X0 X1) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29709 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq29709
    | (have j0 := eq29709 X0 X1
       grind)
    | exact resolve eq29709 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29709
  have eq29877 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29833 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29833
    | (have j0 := eq29833 X0 X1
       grind)
    | exact resolve eq29833 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29833
  have eq29916 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29877 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29877
    | (have j0 := eq29877 X0 X1
       grind)
    | exact resolve eq29877 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29877
  have eq29948 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29916 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29916
    | (have j0 := eq29916 X0 X1
       grind)
    | exact resolve eq29916 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29916
  have eq29965 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29948 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29948
    | (have j0 := eq29948 X0 X1
       grind)
    | exact resolve eq29948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29948
  have eq29978 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29965 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29965
    | (have j0 := eq29965 X0 X1
       grind)
    | exact resolve eq29965 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29965
  have eq30079 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (k X0 X1) X0) X2) X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (k X0 X1) X2
       have i₂ := eq29978 X0 X1
       grind)
    | exact superpose eq29978 eq9
    | (have j1 := eq29978 X0 X1
       grind)
    | exact resolve eq9 eq29978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29978
  have eq47987 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k X0 (k X0 X0))) X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq770 X0 X0 X1
       have i₂ := eq795 X0
       grind)
    | exact superpose eq795 eq770
    | (have j0 := eq770 X0 X0 x
       have j1 := eq795 X0
       grind)
    | exact resolve eq770 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq795
  have eq48098 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k X0 (k X0 X0))) X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq47987 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47987
  have eq48439 : ∀ X0 X1 : G, (M.op (M.op (σ (k (τ X0) (k (τ X0) (τ X0)))) X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48098 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48098
    | exact resolve eq48098 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48098
  have eq48507 : ∀ X0 X1 : G, (M.op (M.op (k X0 (σ (k (τ X0) (τ X0)))) X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48439 X0 X1
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq48439
    | (have j0 := eq48439 X0 X1
       grind)
    | exact resolve eq48439 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq48439
  have eq48536 : ∀ X0 X1 : G, (M.op (M.op (k X0 (k (σ (τ X0)) X0)) X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48507 X0 X1
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq48507
    | (have j0 := eq48507 X0 X1
       grind)
    | exact resolve eq48507 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq48507
  have eq48556 : ∀ X0 X1 : G, (M.op (M.op (k X0 (k X0 X0)) X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48536 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48536
    | (have j0 := eq48536 X0 X1
       grind)
    | exact resolve eq48536 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48536
  have eq48646 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30079 X0 (k X0 X0) X0
       have i₂ := eq48556 X0 X0
       grind)
    | exact superpose eq48556 eq30079
    | (have j0 := eq30079 X0 X0 x
       have j1 := eq48556 X0 x
       grind)
    | exact resolve eq30079 eq48556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48664 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48646 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48646
  have eq49169 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq48664
  have eq49317 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq49169 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49169
  have eq49639 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48556 X0 X1
       have i₂ := eq49317 X0
       grind)
    | exact superpose eq49317 eq48556
    | (have j0 := eq48556 X0 X1
       have j1 := eq49317 X0
       grind)
    | exact resolve eq48556 eq49317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48556 eq49317
  have eq49686 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49639 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49639
  have eq55588 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30079 X0 X0 X0
       have i₂ := eq49686 X0 X0
       grind)
    | exact superpose eq49686 eq30079
    | (have j0 := eq30079 X0 X0 x
       have j1 := eq49686 X0 x
       grind)
    | exact resolve eq30079 eq49686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30079 eq49686
  have eq55607 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55588 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55588
  have eq55639 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq55607
  have eq55824 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55639 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55639
  have eq56152 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55824 (σ X0)
       grind)
    | exact superpose eq55824 eq15
    | exact resolve eq15 eq55824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56215 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56152 X0
       have i₂ := eq55824 X0
       grind)
    | exact superpose eq55824 eq56152
    | exact resolve eq56152 eq55824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55824 eq56152
  have eq57427 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq57575 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq56215 X0
       grind)
    | exact superpose eq56215 eq64
    | exact resolve eq64 eq56215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57739 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57427 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq57427
    | exact resolve eq57427 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57427
  have eq57922 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq57739
  have eq265504 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq327
    | exact resolve eq327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq266323 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq265504 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq265504
    | (have j0 := eq265504 X0 X1
       grind)
    | exact resolve eq265504 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq265504
  have eq267175 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq266323 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq266323
    | (have j0 := eq266323 (σ X1) (σ X0)
       grind)
    | exact resolve eq266323 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266323
  have eq267745 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq267175 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq267175
    | (have j0 := eq267175 X0 X1
       grind)
    | exact resolve eq267175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267175
  have eq267874 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq267745 X0 X1
       have i₂ := eq56215 X1
       grind)
    | exact superpose eq56215 eq267745
    | (have j0 := eq267745 X0 X1
       grind)
    | exact resolve eq267745 eq56215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267745
  have eq267965 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq267874 X0 X1
       have i₂ := eq56215 X0
       grind)
    | exact superpose eq56215 eq267874
    | (have j0 := eq267874 X0 X1
       grind)
    | exact resolve eq267874 eq56215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56215 eq267874
  have eq570334 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq267965 X0 X1
       grind)
    | exact superpose eq267965 eq11
    | (have j1 := eq267965 X0 X1
       grind)
    | exact resolve eq11 eq267965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267965
  have eq588488 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq570334 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq570334 X0 X1
       grind)
    | exact superpose eq570334 eq10
    | (have j1 := eq570334 X0 X1
       grind)
    | exact resolve eq10 eq570334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570334
  have eq588773 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq588488 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq588488
    | (have j0 := eq588488 X0 X1
       grind)
    | exact resolve eq588488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588488
  have eq591787 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq588773 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq588773 X0 X1
       grind)
    | exact superpose eq588773 eq10
    | (have j1 := eq588773 X1 X0
       grind)
    | exact resolve eq10 eq588773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588773
  have eq592070 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq591787 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq591787
    | (have j0 := eq591787 X0 X1
       grind)
    | exact resolve eq591787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591787
  have eq594533 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq592070 y x
       grind)
    | exact superpose eq592070 eq16
    | (have j1 := eq592070 y x
       grind)
    | exact resolve eq16 eq592070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592070
  have eq596267 : y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq7740 x y
       grind)
    | (have r₁ := eq594533
       have r₂ := eq7740 y x
       grind)
    | exact resolve eq594533 eq7740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7740 eq594533
  have eq599782 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq57575 x
       have i₂ := eq596267
       grind)
    | exact superpose eq596267 eq57575
    | exact resolve eq57575 eq596267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57575
  have eq600048 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq596267
       grind)
    | exact superpose eq596267 eq64
    | exact resolve eq64 eq596267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq596267
  have eq602823 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq599782
       grind)
    | exact superpose eq599782 eq16
    | exact resolve eq16 eq599782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599782
  have eq602979 : (σ y) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq602823
       have i₂ := eq600048
       grind)
    | exact superpose eq600048 eq602823
    | exact resolve eq602823 eq600048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600048 eq602823
  have eq602982 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq602979
  have eq602983 : x = (M.op y y) := by grind
  clear eq602982
  have eq603285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57922 y
       have i₂ := eq602983
       grind)
    | exact superpose eq602983 eq57922
    | exact resolve eq57922 eq602983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57922 eq602983
  have eq603568 : False := by grind
  exact eq603568

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_pyy_pxy_pyy_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq53 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq53 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq175 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq180 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq175 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq175 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq175 X0 X0
       have r₂ := eq55 X0 X0
       grind)
    | exact resolve eq175 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq175
  have eq424 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq180 (σ X0) (σ X1)
       grind)
    | exact superpose eq180 eq15
    | exact resolve eq15 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 X1
       have i₂ := eq180 X0 X1
       grind)
    | exact superpose eq180 eq424
    | exact resolve eq424 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq424
  have eq434 : False := by grind
  exact eq434

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq45 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq66
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (M.op X0 X1) X0
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq66
    | exact resolve eq66 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq70 X1 X2 X0
       grind)
    | exact superpose eq70 eq66
    | exact resolve eq66 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq550 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq558 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq824 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq550 x y
       grind)
    | exact superpose eq550 eq16
    | (have j1 := eq550 x y
       grind)
    | exact resolve eq16 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq831 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (σ X1) (σ X0)
       have i₂ := eq550 X1 X0
       grind)
    | exact superpose eq550 eq66
    | (have j1 := eq550 X1 X0
       grind)
    | exact resolve eq66 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq550 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq853 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq855 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq858 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq855 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq855
    | (have j0 := eq855 X0
       grind)
    | exact resolve eq855 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq867 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq853 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq853
    | (have j0 := eq853 (τ X0)
       grind)
    | exact resolve eq853 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq869 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq867 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq867
    | (have j0 := eq867 X0
       grind)
    | exact resolve eq867 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq872 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq869 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq869
    | (have j0 := eq869 X0
       grind)
    | exact resolve eq869 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq1234 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq858 X0
       grind)
    | exact superpose eq858 eq45
    | (have j1 := eq858 X0
       grind)
    | exact resolve eq45 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq858
  have eq1271 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1234 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1234
    | (have j0 := eq1234 X0
       grind)
    | exact resolve eq1234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1303 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (σ (k (τ X0) (τ X0))) = (σ (k (τ X0) (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq1271 (τ X0)
       grind)
    | exact superpose eq1271 eq33
    | (have j1 := eq1271 (τ X0)
       grind)
    | exact resolve eq33 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1315 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1303 X0
       have i₂ := eq18 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq1303
    | (have j0 := eq1303 X0
       grind)
    | exact resolve eq1303 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1303
  have eq1333 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1315 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1315
    | (have j0 := eq1315 X0
       grind)
    | exact resolve eq1315 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1348 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1333 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1333
    | (have j0 := eq1333 X0
       grind)
    | exact resolve eq1333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1475 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) (k X0 X0)) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (k X0 X0) X1
       have i₂ := eq1348 X0
       grind)
    | exact superpose eq1348 eq19
    | (have j1 := eq1348 X0
       grind)
    | exact resolve eq19 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1482 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k (σ X1) X0) = (k (σ X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1475 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1475
    | (have j0 := eq1475 X0 X1
       grind)
    | exact resolve eq1475 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1475
  have eq15715 : ∀ X0 : G, (k (σ X0) (σ X0)) ≠ (k (σ X0) (σ X0)) ∨ (k (σ X0) (σ X0)) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1482 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq15716 : ∀ X0 : G, (k (σ X0) (σ X0)) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq15715 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15715
  have eq15720 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (k X0 (k (τ (σ X0)) X0))) := by
    intro X0
    first
    | (have i₁ := eq15716 X0
       have i₂ := eq22 (σ X0) X0 X0
       grind)
    | exact superpose eq22 eq15716
    | exact resolve eq15716 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15716
  have eq15761 : ∀ X0 : G, (σ (k X0 (k X0 X0))) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15720 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15720
    | exact resolve eq15720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15720
  have eq15801 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq15761 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq15761
    | exact resolve eq15761 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15761
  have eq15924 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq15801 X0
       grind)
    | exact superpose eq15801 eq10
    | exact resolve eq10 eq15801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15801
  have eq15968 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15924 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq15924
    | exact resolve eq15924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15924
  have eq16018 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 (k X0 X0)
       have i₂ := eq15968 X0
       grind)
    | exact superpose eq15968 eq14
    | (have j0 := eq14 X0 (k X0 X0)
       grind)
    | exact resolve eq14 eq15968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16053 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16018
  have eq16943 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (k X0 X0)
       have i₂ := eq16053 X0
       grind)
    | exact superpose eq16053 eq13
    | (have j0 := eq13 X0 (k X0 X0)
       have j1 := eq16053 X0
       grind)
    | (have r₁ := eq13 X0 (k X0 X0)
       have r₂ := eq16053 X0
       grind)
    | exact resolve eq13 eq16053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16053
  have eq16988 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq16943 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16943
  have eq16989 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq16988 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16988
  have eq17031 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq16989 X0
       have i₂ := eq15968 X0
       grind)
    | exact superpose eq15968 eq16989
    | (have j0 := eq16989 X0
       grind)
    | exact resolve eq16989 eq15968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16989
  have eq17032 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq17031 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17031
  have eq17157 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq17032 (σ X0)
       grind)
    | exact superpose eq17032 eq15
    | exact resolve eq15 eq17032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17163 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq17032 (τ X0)
       grind)
    | exact superpose eq17032 eq33
    | exact resolve eq33 eq17032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17212 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17163 X0
       have i₂ := eq17032 X0
       grind)
    | exact superpose eq17032 eq17163
    | exact resolve eq17163 eq17032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17163
  have eq17218 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17157 X0
       have i₂ := eq17032 X0
       grind)
    | exact superpose eq17032 eq17157
    | exact resolve eq17157 eq17032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17157
  have eq17446 : ∀ X0 X1 : G, (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) = (M.op X1 (M.op (M.op (τ X0) X1) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (τ X0) (τ X0)
       have i₂ := eq17212 X0
       grind)
    | exact superpose eq17212 eq88
    | exact resolve eq88 eq17212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17622 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0) (σ X0)
       have i₂ := eq17218 X0
       grind)
    | exact superpose eq17218 eq66
    | exact resolve eq66 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17624 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0) (σ X0)
       have i₂ := eq17218 X0
       grind)
    | exact superpose eq17218 eq68
    | exact resolve eq68 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17625 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) (σ X0) X1
       have i₂ := eq17218 X0
       grind)
    | exact superpose eq17218 eq70
    | exact resolve eq70 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17630 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) = (M.op X1 (M.op (M.op (σ X0) X1) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (σ X0) (σ X0)
       have i₂ := eq17218 X0
       grind)
    | exact superpose eq17218 eq88
    | exact resolve eq88 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19067 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq546 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq546
    | exact resolve eq546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq19185 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19067 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq19067
    | (have j0 := eq19067 X0 X1
       grind)
    | exact resolve eq19067 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19067
  have eq25566 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq558 (M.op (τ X1) X1) X1
       have i₂ := eq66 (τ X1) X1
       grind)
    | exact superpose eq66 eq558
    | (have j0 := eq558 (M.op (τ X0) X1) X0
       grind)
    | exact resolve eq558 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq25789 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25566 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25566
    | (have j0 := eq25566 X0 X1
       grind)
    | exact resolve eq25566 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25566
  have eq25878 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 ∨ (τ (M.op X0 X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25789 X0 X1
       have i₂ := eq17212 X0
       grind)
    | exact superpose eq17212 eq25789
    | (have j0 := eq25789 X0 X1
       grind)
    | exact resolve eq25789 eq17212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25789
  have eq57499 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq824
       have i₂ := eq19185 x y
       grind)
    | exact superpose eq19185 eq824
    | (have j1 := eq19185 (σ x) (σ y)
       grind)
    | (have r₁ := eq824
       have r₂ := eq19185 x y
       grind)
    | exact resolve eq824 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq19185
  have eq57500 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq57499
  have eq57502 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq57500
       have i₂ := eq17218 y
       grind)
    | exact superpose eq17218 eq57500
    | exact resolve eq57500 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57500
  have eq88889 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq831 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq831
    | (have j0 := eq831 (τ X0) (τ X1)
       grind)
    | exact resolve eq831 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq831
  have eq89250 : ∀ X0 X1 : G, (M.op (σ (τ (k X0 X1))) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq88889 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88889
    | (have j0 := eq88889 X0 X1
       grind)
    | exact resolve eq88889 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88889
  have eq89372 : ∀ X0 X1 : G, (M.op (k X0 X1) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq89250 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq89250
    | (have j0 := eq89250 X0 X1
       grind)
    | exact resolve eq89250 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89250
  have eq89488 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op (k X0 X1) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq89372 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89372
    | (have j0 := eq89372 X0 X1
       grind)
    | exact resolve eq89372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89372
  have eq89597 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op (k X0 X1) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq89488 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89488
    | (have j0 := eq89488 X0 X1
       grind)
    | exact resolve eq89488 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89488
  have eq89669 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (σ (τ X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op (k X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89597 X0 X1
       have i₂ := eq17218 (τ X0)
       grind)
    | exact superpose eq17218 eq89597
    | (have j0 := eq89597 X0 X1
       grind)
    | exact resolve eq89597 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89597
  have eq89736 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op (k X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89669 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq89669
    | (have j0 := eq89669 X0 X1
       grind)
    | exact resolve eq89669 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89669
  have eq89782 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op (k X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89736 X0 X1
       have i₂ := eq17212 X0
       grind)
    | exact superpose eq17212 eq89736
    | (have j0 := eq89736 X0 X1
       grind)
    | exact resolve eq89736 eq17212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17212 eq89736
  have eq89814 : ∀ X0 X1 : G, (M.op (k X0 X1) X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89782 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq89782
    | (have j0 := eq89782 X0 X1
       grind)
    | exact resolve eq89782 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89782
  have eq90042 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66 (k X1 X0) X0
       have i₂ := eq89814 X1 X0
       grind)
    | exact superpose eq89814 eq66
    | (have j1 := eq89814 X1 X0
       grind)
    | exact resolve eq66 eq89814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89814
  have eq378778 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25878 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25878
    | exact resolve eq25878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25878
  have eq379272 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X0 X1))) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq378778 X0 X1
       have i₂ := eq15 X0 (M.op X0 X1)
       grind)
    | exact superpose eq15 eq378778
    | (have j0 := eq378778 X0 X1
       grind)
    | exact resolve eq378778 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378778
  have eq379464 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq379272 X0 X1
       have i₂ := eq17218 X0
       grind)
    | exact superpose eq17218 eq379272
    | (have j0 := eq379272 X0 X1
       grind)
    | exact resolve eq379272 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379272
  have eq379646 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq379464 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq379464
    | (have j0 := eq379464 X0 X1
       grind)
    | exact resolve eq379464 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379464
  have eq380897 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (σ (k (M.op X0 X1) X0)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq379646 (M.op X0 X1) X0
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq379646
    | (have j0 := eq379646 X0 X1
       grind)
    | exact resolve eq379646 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664164 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq57502
       grind)
    | exact superpose eq57502 eq68
    | exact resolve eq68 eq57502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57502
  have eq745798 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq70 (σ x) (σ y) X0
       have i₂ := eq664164
       grind)
    | exact superpose eq664164 eq70
    | exact resolve eq70 eq664164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq664164
  have eq746179 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq745798 X0
       have i₂ := eq66 (σ x) X0
       grind)
    | exact superpose eq66 eq745798
    | exact resolve eq745798 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745798
  have eq746379 : ∀ X0 : G, (τ (σ x)) = (M.op y y) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq746179 X0
       grind)
    | exact superpose eq746179 eq10
    | (have j1 := eq746179 X0
       grind)
    | exact resolve eq10 eq746179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746179
  have eq746775 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq746379 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq746379
    | (have j0 := eq746379 X0
       grind)
    | exact resolve eq746379 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746379
  have eq746776 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op y y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq746775 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746775
  have eq747084 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op X0 (M.op (M.op x X0) x)) ∨ x = (M.op y y) ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 x x
       have i₂ := eq746776 X0
       grind)
    | exact superpose eq746776 eq88
    | (have j1 := eq746776 X1
       grind)
    | exact resolve eq88 eq746776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746776
  have eq747332 : ∀ X0 X1 : G, x = (M.op y y) ∨ x = (M.op X0 x) ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq747084 X1 X1
       have i₂ := eq66 x X1
       grind)
    | exact superpose eq66 eq747084
    | (have j0 := eq747084 X0 X1
       grind)
    | exact resolve eq747084 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747084
  have eq747545 : ∀ X0 X1 : G, x = (k y x) ∨ x = (M.op X0 x) ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    grind
  have eq747839 : ∀ X0 X1 : G, x = (M.op y x) ∨ x = (M.op X0 x) ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 y y
       have i₂ := eq747332 X0 X1
       grind)
    | exact superpose eq747332 eq68
    | (have j1 := eq747332 y X1
       grind)
    | exact resolve eq68 eq747332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq747332
  have eq749081 : ∀ X0 : G, x ≠ x ∨ x = (M.op y x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq747839 y X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747839
  have eq749082 : ∀ X0 : G, x = (M.op y x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq749081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749081
  have eq749085 : ∀ X0 X1 X2 : G, (M.op (σ x) X2) = X2 ∨ (M.op (M.op (M.op X0 X1) (M.op (M.op x X0) y)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 y x X1
       have i₂ := eq749082 X2
       grind)
    | exact superpose eq749082 eq64
    | (have j1 := eq749082 X2
       grind)
    | exact resolve eq64 eq749082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq749082
  have eq758784 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (σ x)) X0) (τ (σ x))) = (M.op X0 (M.op (M.op (τ (σ x)) X0) (τ (σ x)))) ∨ (M.op (M.op (M.op X1 X2) (M.op (M.op x X1) y)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17446 (σ x) X1
       have i₂ := eq749085 X0 X1 (σ x)
       grind)
    | exact superpose eq749085 eq17446
    | (have j1 := eq749085 X1 X2 X2
       grind)
    | exact resolve eq17446 eq749085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17446 eq749085
  have eq759435 : ∀ X0 X1 X2 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ (M.op (M.op (M.op X1 X2) (M.op (M.op x X1) y)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq758784 X1 X1 X2
       have i₂ := eq66 (τ (σ x)) X1
       grind)
    | exact superpose eq66 eq758784
    | (have j0 := eq758784 X0 X1 X2
       grind)
    | exact resolve eq758784 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758784
  have eq759537 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op x X1) y)) X2) = X2 ∨ x = (M.op X0 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq759435 X0 X1 X2
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq759435
    | (have j0 := eq759435 X0 X1 X2
       grind)
    | exact resolve eq759435 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759435
  have eq760434 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op (M.op X0 x) (M.op (M.op x X0) y)) x) := by
    intro X0
    first
    | (have j0 := eq759537 (M.op (M.op X0 x) (M.op (M.op x X0) y)) X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759537
  have eq760435 : ∀ X0 : G, x = (M.op (M.op (M.op X0 x) (M.op (M.op x X0) y)) x) := by
    intro X0
    first
    | (have j0 := eq760434 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760434
  have eq760849 : x = (M.op (M.op (M.op x x) y) x) := by
    first
    | (have i₁ := eq67 (M.op (M.op x x) y) x x
       have i₂ := eq760435 x
       grind)
    | exact superpose eq760435 eq67
    | exact resolve eq67 eq760435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760435
  have eq761184 : y = (M.op x y) := by
    first
    | (have i₁ := eq9 y x x
       have i₂ := eq760849
       grind)
    | exact superpose eq760849 eq9
    | exact resolve eq9 eq760849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761186 : x = (M.op y x) := by
    first
    | (have i₁ := eq67 y x x
       have i₂ := eq760849
       grind)
    | exact superpose eq760849 eq67
    | exact resolve eq67 eq760849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq760849
  have eq761653 : x = y ∨ y = (M.op x x) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq379646 x y
       have i₂ := eq761184
       grind)
    | exact superpose eq761184 eq379646
    | exact resolve eq379646 eq761184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379646
  have eq761660 : x = y ∨ x = (M.op y y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq380897 x y
       have i₂ := eq761184
       grind)
    | exact superpose eq761184 eq380897
    | exact resolve eq380897 eq761184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380897
  have eq770445 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq761653
       grind)
    | exact superpose eq761653 eq16
    | exact resolve eq16 eq761653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761653
  have eq770541 : (σ x) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq770445
       have r₂ := eq17218 x
       grind)
    | exact resolve eq770445 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770445
  have eq770558 : (τ (σ x)) = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq770541
       grind)
    | exact superpose eq770541 eq10
    | exact resolve eq10 eq770541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770565 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (k x y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq24 X0 (k x y)
       have i₂ := eq770541
       grind)
    | exact superpose eq770541 eq24
    | exact resolve eq24 eq770541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770541
  have eq770958 : ∀ X0 : G, (k (τ X0) x) = (k (τ X0) (k x y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq770565 X0
       have i₂ := eq24 X0 x
       grind)
    | exact superpose eq24 eq770565
    | exact resolve eq770565 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770565
  have eq770965 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq770558
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq770558
    | exact resolve eq770558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770558
  have eq771071 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq761660
       grind)
    | exact superpose eq761660 eq16
    | exact resolve eq16 eq761660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761660
  have eq771163 : (σ y) = (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq771071
       have r₂ := eq17218 x
       grind)
    | exact resolve eq771071 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17218 eq771071
  have eq771197 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (k X0 (σ y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq24 X0 (k y x)
       have i₂ := eq771163
       grind)
    | exact superpose eq771163 eq24
    | exact resolve eq24 eq771163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771202 : ∀ X0 : G, (k (k y x) (τ X0)) = (τ (k (σ y) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq30 (k y x) X0
       have i₂ := eq771163
       grind)
    | exact superpose eq771163 eq30
    | exact resolve eq30 eq771163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771163
  have eq771585 : ∀ X0 : G, (k y (τ X0)) = (k (k y x) (τ X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq771202 X0
       have i₂ := eq30 y X0
       grind)
    | exact superpose eq30 eq771202
    | exact resolve eq771202 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq771202
  have eq771590 : ∀ X0 : G, (k (τ X0) y) = (k (τ X0) (k y x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq771197 X0
       have i₂ := eq24 X0 y
       grind)
    | exact superpose eq24 eq771197
    | exact resolve eq771197 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq771197
  have eq773892 : ∀ X0 : G, y = (M.op x x) ∨ (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq770958 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq770958
    | exact resolve eq770958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770958
  have eq774286 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq17624 x
       have i₂ := eq773892 X0
       grind)
    | exact superpose eq773892 eq17624
    | (have j1 := eq773892 X0
       grind)
    | exact resolve eq17624 eq773892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17624 eq773892
  have eq776196 : ∀ X0 : G, x = (M.op y y) ∨ (k y X0) = (k (k y x) X0) := by
    intro X0
    first
    | (have i₁ := eq771585 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq771585
    | exact resolve eq771585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771585
  have eq776562 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k y X0) = (k (k y x) X0) := by
    intro X0
    first
    | (have i₁ := eq17622 y
       have i₂ := eq776196 X0
       grind)
    | exact superpose eq776196 eq17622
    | (have j1 := eq776196 X0
       grind)
    | exact resolve eq17622 eq776196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776196
  have eq777119 : ∀ X0 : G, x = (M.op y y) ∨ (k X0 y) = (k X0 (k y x)) := by
    intro X0
    first
    | (have i₁ := eq771590 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq771590
    | exact resolve eq771590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771590
  have eq777512 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = (k X0 (k y x)) := by
    intro X0
    first
    | (have i₁ := eq17622 y
       have i₂ := eq777119 X0
       grind)
    | exact superpose eq777119 eq17622
    | (have j1 := eq777119 X0
       grind)
    | exact resolve eq17622 eq777119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17622 eq777119
  have eq904906 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq774286 X0
       grind)
    | exact superpose eq774286 eq16
    | (have j1 := eq774286 X0
       grind)
    | exact resolve eq16 eq774286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774286
  have eq905207 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq904906 X0
       have i₂ := eq761184
       grind)
    | exact superpose eq761184 eq904906
    | (have j0 := eq904906 X0
       grind)
    | exact resolve eq904906 eq761184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904906
  have eq905208 : ∀ X0 : G, (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have j0 := eq905207 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905207
  have eq947614 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k y X0) = (k (k y x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq776562 X0
       grind)
    | exact superpose eq776562 eq16
    | (have j1 := eq776562 X0
       grind)
    | exact resolve eq16 eq776562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776562
  have eq947914 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k y X0) = (k (k y x) X0) := by
    intro X0
    first
    | (have i₁ := eq947614 X0
       have i₂ := eq761184
       grind)
    | exact superpose eq761184 eq947614
    | (have j0 := eq947614 X0
       grind)
    | exact resolve eq947614 eq761184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947614
  have eq947915 : ∀ X0 : G, (k y X0) = (k (k y x) X0) := by
    intro X0
    first
    | (have j0 := eq947914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947914
  have eq947942 : ∀ X0 X1 X2 : G, (M.op (σ x) X2) = X2 ∨ x = (M.op X1 x) ∨ (k x X0) = (k y X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq947915 X0
       have i₂ := eq747545 X1 X2
       grind)
    | exact superpose eq747545 eq947915
    | (have j1 := eq747545 X1 X2
       grind)
    | exact resolve eq947915 eq747545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747545 eq947915
  have eq1026330 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 y) = (k X0 (k y x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq777512 X0
       grind)
    | exact superpose eq777512 eq16
    | (have j1 := eq777512 X0
       grind)
    | exact resolve eq16 eq777512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777512
  have eq1026630 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (k X0 (k y x)) := by
    intro X0
    first
    | (have i₁ := eq1026330 X0
       have i₂ := eq761184
       grind)
    | exact superpose eq761184 eq1026330
    | (have j0 := eq1026330 X0
       grind)
    | exact resolve eq1026330 eq761184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026330
  have eq1026631 : ∀ X0 : G, (k X0 y) = (k X0 (k y x)) := by
    intro X0
    first
    | (have j0 := eq1026630 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026630
  have eq1307265 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op X0 x) ∨ (k x X1) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq947942 X1 X0 (σ y)
       grind)
    | exact superpose eq947942 eq16
    | (have j1 := eq947942 X1 X0 x
       grind)
    | exact resolve eq16 eq947942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947942
  have eq1307995 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ x = (M.op X0 x) ∨ (k x X1) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1307265 X0 X1
       have i₂ := eq761184
       grind)
    | exact superpose eq761184 eq1307265
    | (have j0 := eq1307265 X0 X1
       grind)
    | exact resolve eq1307265 eq761184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307265
  have eq1307996 : ∀ X0 X1 : G, (k x X1) = (k y X1) ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have j0 := eq1307995 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307995
  have eq1308373 : ∀ X0 X1 : G, (k X0 (k x x)) = (k X0 y) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1026631 X0
       have i₂ := eq1307996 X1 x
       grind)
    | exact superpose eq1307996 eq1026631
    | (have j1 := eq1307996 X1 X1
       grind)
    | exact resolve eq1026631 eq1307996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1308399 : ∀ X0 : G, y ≠ (k x y) ∨ y = (M.op y y) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq872 y
       have i₂ := eq1307996 X0 y
       grind)
    | exact superpose eq1307996 eq872
    | (have j0 := eq872 y
       have j1 := eq1307996 X0 x
       grind)
    | exact resolve eq872 eq1307996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq1308814 : ∀ X0 : G, (k x y) = (k y (k x y)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq15968 y
       have i₂ := eq1307996 X0 y
       grind)
    | exact superpose eq1307996 eq15968
    | (have j1 := eq1307996 X0 x
       grind)
    | exact resolve eq15968 eq1307996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15968 eq1307996
  have eq1309914 : ∀ X0 : G, (k y x) = (k x y) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1308814 X0
       have i₂ := eq905208 y
       grind)
    | exact superpose eq905208 eq1308814
    | (have j0 := eq1308814 X0
       grind)
    | exact resolve eq1308814 eq905208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308814
  have eq1310341 : ∀ X0 X1 : G, (k X0 y) = (k X0 (M.op x x)) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1308373 X0 X1
       have i₂ := eq17032 x
       grind)
    | exact superpose eq17032 eq1308373
    | (have j0 := eq1308373 X0 X1
       grind)
    | exact resolve eq1308373 eq17032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308373
  have eq1311515 : ∀ X0 X1 : G, (k X0 y) = (k X0 (k x y)) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1026631 X0
       have i₂ := eq1309914 X1
       grind)
    | exact superpose eq1309914 eq1026631
    | (have j1 := eq1309914 X1
       grind)
    | exact resolve eq1026631 eq1309914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026631 eq1309914
  have eq1311630 : ∀ X0 X1 : G, (k X0 x) = (k X0 y) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1311515 X0 X1
       have i₂ := eq905208 X0
       grind)
    | exact superpose eq905208 eq1311515
    | (have j0 := eq1311515 X0 X1
       grind)
    | exact resolve eq1311515 eq905208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905208 eq1311515
  have eq1312680 : ∀ X0 : G, x = (k x x) ∨ y = (M.op x x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq770965
       have i₂ := eq1311630 x X0
       grind)
    | exact superpose eq1311630 eq770965
    | (have j1 := eq1311630 X0 X0
       grind)
    | exact resolve eq770965 eq1311630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770965 eq1311630
  have eq1312883 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1312680 X0
       have i₂ := eq17032 x
       grind)
    | exact superpose eq17032 eq1312680
    | (have j0 := eq1312680 x
       grind)
    | exact resolve eq1312680 eq17032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17032 eq1312680
  have eq1343804 : ∀ X0 : G, (M.op x x) = (k x y) ∨ x = (M.op X0 x) := by
    intro X0
    grind
  clear eq1310341
  have eq1388552 : ∀ X0 X1 : G, y ≠ (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op X0 x) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1308399 X0
       have i₂ := eq1343804 X1
       grind)
    | exact superpose eq1343804 eq1308399
    | (have j0 := eq1308399 X0
       have j1 := eq1343804 X0
       grind)
    | exact resolve eq1308399 eq1343804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308399 eq1343804
  have eq1393034 : ∀ X0 : G, y = (k x y) ∨ x = (M.op x x) ∨ x = (M.op X0 x) := by
    intro X0
    grind
  have eq1393548 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq1312883 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312883
  have eq1393549 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq1393548
  have eq1404069 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq90042 y x
       have i₂ := eq1393034 X0
       grind)
    | exact superpose eq1393034 eq90042
    | (have j0 := eq90042 y y
       have j1 := eq1393034 x
       grind)
    | exact resolve eq90042 eq1393034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90042 eq1393034
  have eq1404113 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1404069 x
       have j1 := eq1388552 x x
       grind)
    | (have r₁ := eq1404069 X0
       have r₂ := eq1388552 X0 x
       grind)
    | exact resolve eq1404069 eq1388552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388552 eq1404069
  have eq1404143 : ∀ X0 : G, x = y ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1404113 X0
       have i₂ := eq761186
       grind)
    | exact superpose eq761186 eq1404113
    | (have j0 := eq1404113 x
       grind)
    | exact resolve eq1404113 eq761186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761186 eq1404113
  have eq1404151 : ∀ X0 : G, x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1404143 x
       grind)
    | (have r₁ := eq1404143 X0
       have r₂ := eq1393549
       grind)
    | exact resolve eq1404143 eq1393549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393549 eq1404143
  have eq1410143 : x ≠ x ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq1404151 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404151
  have eq1410144 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq1410143
  have eq1410901 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq88 X0 y y
       have i₂ := eq1410144
       grind)
    | exact superpose eq1410144 eq88
    | exact resolve eq88 eq1410144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq1410144
  have eq1411180 : ∀ X0 : G, x = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1410901 x
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq1410901
    | exact resolve eq1410901 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410901
  have eq1411635 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq17625 x X0
       have i₂ := eq1411180 X1
       grind)
    | exact superpose eq1411180 eq17625
    | (have j1 := eq1411180 X1
       grind)
    | exact resolve eq17625 eq1411180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17625 eq1411180
  have eq1412281 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1411635 X0 X1
       have i₂ := eq66 (σ x) X0
       grind)
    | exact superpose eq66 eq1411635
    | (have j0 := eq1411635 X0 X1
       grind)
    | exact resolve eq1411635 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411635
  have eq1426076 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1412281 (σ y) X0
       grind)
    | exact superpose eq1412281 eq16
    | (have j1 := eq1412281 X0 X0
       grind)
    | exact resolve eq16 eq1412281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412281
  have eq1426792 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1426076 X0
       have i₂ := eq761184
       grind)
    | exact superpose eq761184 eq1426076
    | (have j0 := eq1426076 X0
       grind)
    | exact resolve eq1426076 eq761184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761184 eq1426076
  have eq1426793 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1426792 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426792
  have eq1426979 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq17630 y x
       have i₂ := eq1426793 y
       grind)
    | exact superpose eq1426793 eq17630
    | exact resolve eq17630 eq1426793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17630
  have eq1428616 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1426979 x
       have i₂ := eq66 (σ y) x
       grind)
    | exact superpose eq66 eq1426979
    | exact resolve eq1426979 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1426979
  have eq1437666 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1428616 (σ x)
       grind)
    | exact superpose eq1428616 eq16
    | exact resolve eq16 eq1428616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428616
  have eq1438029 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1437666
       have i₂ := eq1426793 x
       grind)
    | exact superpose eq1426793 eq1437666
    | exact resolve eq1437666 eq1426793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426793 eq1437666
  have eq1438030 : False := by grind
  exact eq1438030

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_y_pyx_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  clear eq36
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq22941 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq22941
    | exact resolve eq22941 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22941
  have eq22953 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22942
       have r₂ := eq28
       grind)
    | exact resolve eq22942 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22942
  have eq22955 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq22953
    | exact resolve eq22953 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22953
  have eq22962 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22955 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq22955
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq22955
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq22955
       grind)
    | exact resolve eq12 eq22955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22955
  have eq23020 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq22962
  have eq23024 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq23020
       have r₂ := eq27
       grind)
    | exact resolve eq23020 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23020
  have eq23449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23024 eq96
    | exact resolve eq96 eq23024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23024
  have eq23458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq23449
  have eq23461 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq23458
       have r₂ := eq28
       grind)
    | exact resolve eq23458 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23458
  have eq23466 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by grind
  have eq23472 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq23461 eq51
    | exact resolve eq51 eq23461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23461
  have eq23528 : (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq23472
    | exact resolve eq23472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23472
  have eq23791 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq23528
       grind)
    | exact superpose eq23528 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq23528
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq23528
       grind)
    | exact resolve eq12 eq23528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23528
  have eq23849 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23791
  have eq23853 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23849
       have r₂ := eq19
       grind)
    | exact resolve eq23849 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23849
  have eq24016 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq23853
       grind)
    | exact superpose eq23853 eq45
    | exact resolve eq45 eq23853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23853
  have eq24036 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq24016
    | exact resolve eq24016 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24016
  have eq24049 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24036 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq24036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq24049
    | exact resolve eq24049 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24049
  have eq24063 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24052
       have r₂ := eq28
       grind)
    | exact resolve eq24052 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24052
  have eq24065 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq24063
    | exact resolve eq24063 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24063
  have eq24074 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq23466 eq96
    | exact resolve eq96 eq23466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq23466
  have eq24086 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq24074
  have eq24104 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq24086
       grind)
    | exact superpose eq24086 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq24086
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq24086
       grind)
    | exact resolve eq12 eq24086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24086
  have eq24162 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq24104
  have eq24166 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq24162
       have r₂ := eq19
       grind)
    | exact resolve eq24162 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24162
  have eq24827 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq24166
       grind)
    | exact superpose eq24166 eq45
    | exact resolve eq45 eq24166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24166
  have eq24847 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq24827
    | exact resolve eq24827 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24827
  have eq24862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24847 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq24847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq24862
    | exact resolve eq24862 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24862
  have eq24878 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq24867
       have r₂ := eq28
       grind)
    | exact resolve eq24867 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24867
  have eq24880 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq24878
    | exact resolve eq24878 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24878
  have eq34775 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24065 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq24065
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq24065
       grind)
    | exact resolve eq12 eq24065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24065
  have eq34840 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34775
  have eq34846 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34840
       have r₂ := eq27
       grind)
    | exact resolve eq34840 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34840
  have eq39043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34846 eq24036
    | exact resolve eq24036 eq34846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24036 eq34846
  have eq39066 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq39043
  have eq39086 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq39066
       have r₂ := eq28
       grind)
    | exact resolve eq39066 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39066
  have eq39603 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq39086 eq51
    | exact resolve eq51 eq39086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39086
  have eq39675 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq39603
    | exact resolve eq39603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39603
  have eq39676 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39675
  have eq39683 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39676
  have eq40237 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq39683
       grind)
    | exact superpose eq39683 eq45
    | exact resolve eq45 eq39683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq39683
  have eq40279 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40237
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40237
    | exact resolve eq40237 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40237
  have eq40955 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40279 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq40279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40970 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq40955
    | exact resolve eq40955 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40955
  have eq40971 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq40970
  have eq40983 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq40971
    | exact resolve eq40971 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40971
  have eq43535 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq40983 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq40983
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq40983
       grind)
    | exact resolve eq12 eq40983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40983
  have eq43611 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43535
  have eq43617 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq43611
       have r₂ := eq27
       grind)
    | exact resolve eq43611 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43611
  have eq43878 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43617 eq40279
    | exact resolve eq40279 eq43617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40279 eq43617
  have eq43881 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43878
  have eq43914 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43881 eq51
    | exact resolve eq51 eq43881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43881
  have eq43988 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq43914
    | exact resolve eq43914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq43914
  have eq43989 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43988
  have eq43991 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq43989 eq28
    | exact resolve eq28 eq43989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq43993 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq43989 eq53
    | exact resolve eq53 eq43989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq44063 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq43993 eq24880
    | exact resolve eq24880 eq43993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24880
  have eq44168 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq44063
       have r₂ := eq43991
       grind)
    | exact resolve eq44063 eq43991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44063
  have eq44176 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq43989 eq44168
    | exact resolve eq44168 eq43989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43989 eq44168
  have eq48825 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq44176
  have eq49983 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq48825 eq24847
    | exact resolve eq24847 eq48825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24847 eq48825
  have eq49994 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq49983
  have eq50020 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq49994
       have r₂ := eq43991
       grind)
    | exact resolve eq49994 eq43991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49994
  have eq50052 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51 y y
       have i₂ := eq50020
       grind)
    | exact superpose eq50020 eq51
    | exact resolve eq51 eq50020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq50020
  have eq50149 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50052
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq50052
    | exact resolve eq50052 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50052
  have eq50157 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50149 eq30
    | exact resolve eq30 eq50149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq50149
  have eq50456 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq50157
    | exact resolve eq50157 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50157
  have eq50712 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq50456 eq21
    | exact resolve eq21 eq50456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50456
  have eq50963 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq50712
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq50712
    | exact resolve eq50712 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50712
  have eq50966 : x = y := by
    first
    | (have r₁ := eq50963
       have r₂ := eq43991
       grind)
    | exact resolve eq50963 eq43991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50963
  have eq51217 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq50966
       grind)
    | exact superpose eq50966 eq19
    | exact resolve eq19 eq50966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq51218 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq50966
       grind)
    | exact superpose eq50966 eq25
    | exact resolve eq25 eq50966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq50966
  have eq51489 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq51218
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq51218
    | exact resolve eq51218 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51218
  have eq51639 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq51489 eq43991
    | exact resolve eq43991 eq51489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43991
  have eq51641 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq51489 eq43993
    | exact resolve eq43993 eq51489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43993 eq51489
  have eq52536 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq51641
  have eq53584 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq52536 eq73
    | exact resolve eq73 eq52536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq52536
  have eq53607 : x = (k x x) := by
    first
    | exact superpose eq29 eq53584
    | exact resolve eq53584 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq53584
  have eq58221 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq82 x
       have i₂ := eq53607
       grind)
    | exact superpose eq53607 eq82
    | (have j0 := eq82 x
       grind)
    | exact resolve eq82 eq53607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq53607
  have eq58222 : x = (M.op x x) := by grind
  clear eq58221
  have eq58225 : x = (M.op x y) := by
    first
    | (have i₁ := eq58222
       have i₂ := eq51217
       grind)
    | exact superpose eq51217 eq58222
    | exact resolve eq58222 eq51217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51217 eq58222
  have eq58251 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq58225 eq21
    | exact resolve eq21 eq58225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq58225
  have eq58563 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq58251
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq58251
    | exact resolve eq58251 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq58251
  have eq58639 : False := by grind
  exact eq58639

/-- `Equation3201`: `x = (((y ◇ z) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pyx_x_pxy_Equation3201 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3201 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3201.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) y) X0) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : y ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq978 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq979 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1005 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1004 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1024 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq978
       grind)
    | exact superpose eq978 eq40
    | exact resolve eq40 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq1025 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1024
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1024
    | exact resolve eq1024 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1027 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1025
    | exact resolve eq1025 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1027 eq979
    | exact resolve eq979 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq1027
  have eq1042 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1035
       have r₂ := eq27
       grind)
    | exact resolve eq1035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1047 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1042 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1042
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1042
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1042
       grind)
    | exact resolve eq13 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1051 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1047
  have eq1057 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1051 eq152
    | exact resolve eq152 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1051
  have eq1060 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1057
    | exact resolve eq1057 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1057
  have eq1063 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1006 y
       grind)
    | (have r₁ := eq1060
       have r₂ := eq1006 y
       grind)
    | exact resolve eq1060 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1067 : y ≠ y ∨ y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1063
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1063
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1063
       grind)
    | exact resolve eq13 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 : G, (M.op (M.op (M.op y y) y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq16
    | exact resolve eq16 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1067
  have eq1073 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1063 eq1068
    | exact resolve eq1068 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1074 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1063 eq1073
    | exact resolve eq1073 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063 eq1073
  have eq1076 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq40
    | exact resolve eq40 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1071
  have eq1079 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1076
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1076
    | exact resolve eq1076 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1082 : ∀ X0 : G, X0 ≠ X0 ∨ (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1074 X0
       grind)
    | exact superpose eq1074 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y X0
       have r₂ := eq1074 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1074 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1074 X0
       grind)
    | exact resolve eq13 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1088 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1082 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1095 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1079 eq1006
    | (have j0 := eq1006 (σ y)
       grind)
    | (have r₁ := eq1006 (σ y)
       have r₂ := eq1079
       grind)
    | exact resolve eq1006 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq1096 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1095
  have eq1102 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1096 eq16
    | exact resolve eq16 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1107 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1096 eq1102
    | exact resolve eq1102 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1108 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1096 eq1107
    | exact resolve eq1107 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096 eq1107
  have eq1110 : ∀ X0 : G, X0 ≠ X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1108 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) X0
       have r₂ := eq1108 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1108 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1108 X0
       grind)
    | exact resolve eq13 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1116 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1144 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1088 x
       grind)
    | exact superpose eq1088 eq18
    | (have j1 := eq1088 x
       grind)
    | exact resolve eq18 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1175 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1144
       grind)
    | exact superpose eq1144 eq39
    | exact resolve eq39 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1176 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1175
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1175
    | exact resolve eq1175 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1178 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1176
    | exact resolve eq1176 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1231 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1116 eq26
    | (have j1 := eq1116 (σ x)
       grind)
    | exact resolve eq26 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1178 eq1231
    | exact resolve eq1231 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq1231
  have eq1259 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1243
       have r₂ := eq27
       grind)
    | exact resolve eq1243 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1269 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1259 eq175
    | exact resolve eq175 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1259
  have eq1294 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f1294_13 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
      intro X0
      grind
    have f1294_20 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f1294_21 : X0 ≠ (M.op (σ x) X0) := by grind
    have f1294_22 : y ≠ (M.op x y) := by grind
    have f1294_23 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 := by
      intro X0
      first
      | (have j0 := f1294_13 X0
         grind)
      | (have r₁ := f1294_13 X0
         have r₂ := f1294_22
         grind)
      | exact resolve f1294_13 f1294_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1294_51 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f1294_20 X0 (σ y) (σ x)
         have i₂ := f1294_23 (σ x)
         grind)
      | exact superpose f1294_23 f1294_20
      | exact resolve f1294_20 f1294_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1294_55 : X0 ≠ X0 := by
      first
      | (have i₁ := f1294_21
         have i₂ := f1294_51 X0
         grind)
      | exact superpose f1294_51 f1294_21
      | (have r₁ := f1294_21
         have r₂ := f1294_51 X0
         grind)
      | exact resolve f1294_21 f1294_51
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1294_60 : False := by grind
    exact f1294_60
  clear eq1269
  have eq1325 : ∀ X0 : G, X0 ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1294 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) X0
       have r₂ := eq1294 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1294 X0
       grind)
    | exact resolve eq13 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1333 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1364 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1333 eq1294
    | exact resolve eq1294 eq1333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq1333
  have eq1371 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1364
  have eq1404 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1371 eq141
    | exact resolve eq141 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1371
  have eq1407 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1404
    | exact resolve eq1404 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1404
  have eq1412 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1006 x
       have i₂ := eq1407
       grind)
    | exact superpose eq1407 eq1006
    | (have j0 := eq1006 x
       grind)
    | (have r₁ := eq1006 x
       have r₂ := eq1407
       grind)
    | exact resolve eq1006 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq1407
  have eq1413 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq1412
  have eq1419 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq1413
       grind)
    | exact superpose eq1413 eq16
    | exact resolve eq16 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1423 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1413 eq1419
    | exact resolve eq1419 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq1424 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1413 eq1423
    | exact resolve eq1423 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413 eq1423
  have eq1430 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1424 y
       grind)
    | exact superpose eq1424 eq18
    | (have j1 := eq1424 y
       grind)
    | exact resolve eq18 eq1424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1424
  have eq1444 : y = (M.op x y) := by grind
  clear eq1430
  have eq1592 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1444
       grind)
    | exact superpose eq1444 eq24
    | exact resolve eq24 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1595 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq1444
       grind)
    | exact superpose eq1444 eq174
    | exact resolve eq174 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1596 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq178
       have i₂ := eq1444
       grind)
    | exact superpose eq1444 eq178
    | (have r₁ := eq178
       have r₂ := eq1444
       grind)
    | exact resolve eq178 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1444
  have eq1598 : (k x (M.op x y)) = (M.op (M.op x y) x) := by grind
  clear eq1596
  have eq1599 : ∀ X0 : G, (M.op (M.op (k x (M.op x y)) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1598 eq1595
    | exact resolve eq1595 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1601 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1592 eq20
    | exact resolve eq20 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1592
  have eq1721 : ∀ X0 : G, (M.op (M.op (M.op (k x (M.op x y)) (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1598 eq16
    | exact resolve eq16 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1722 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq1599 eq1721
    | exact resolve eq1721 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599 eq1721
  have eq1736 : ∀ X0 : G, X0 ≠ X0 ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1722 X0
       grind)
    | exact superpose eq1722 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x X0
       have r₂ := eq1722 X0
       grind)
    | exact resolve eq13 eq1722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1744 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1736 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq1786 : x = (k x x) := by
    first
    | (have i₁ := eq1722 x
       have i₂ := eq1744 x
       grind)
    | exact superpose eq1744 eq1722
    | exact resolve eq1722 eq1744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722 eq1744
  have eq1825 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1786
       grind)
    | exact superpose eq1786 eq39
    | exact resolve eq39 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1786
  have eq1831 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1825
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1825
    | exact resolve eq1825 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1825
  have eq1868 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1831 eq1005
    | (have j0 := eq1005 (σ x) (σ x)
       grind)
    | (have r₁ := eq1005 (σ x) (σ x)
       have r₂ := eq1831
       grind)
    | exact resolve eq1005 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq1831
  have eq1869 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1868
  have eq1870 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1869
  have eq1928 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1870 eq16
    | exact resolve eq16 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1932 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1870 eq1928
    | exact resolve eq1928 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928
  have eq1934 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1870 eq1932
    | exact resolve eq1932 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870 eq1932
  have eq1942 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1934 eq26
    | (have j1 := eq1934 (σ y)
       grind)
    | exact resolve eq26 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1934
  have eq1964 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1942 eq27
    | exact resolve eq27 eq1942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1942
  have eq1966 : False := by grind
  exact eq1966

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq38 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
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
  clear eq36
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq39
    | exact resolve eq39 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq39
  have eq79 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq88
  have eq297 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq302 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq307 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq302 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq302 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq302 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq324 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq307
    | (have j0 := eq307 X0 X1
       grind)
    | exact resolve eq307 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq325 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq324 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq724 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq325
    | (have j0 := eq325 (τ X0) X1
       grind)
    | exact resolve eq325 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq748 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq724 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq724
    | (have j0 := eq724 X0 X1
       grind)
    | exact resolve eq724 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq724
  have eq755 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq748 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq748
    | (have j0 := eq748 X0 X1
       grind)
    | exact resolve eq748 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq748
  have eq761 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq755 X0 X1
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq755 X1 X0
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq755 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq755
  have eq766 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq761 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq761
    | exact resolve eq761 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq761 (σ X1) X0
       grind)
    | exact superpose eq761 eq15
    | exact resolve eq15 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq1075 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq773 x y
       grind)
    | exact superpose eq773 eq16
    | exact resolve eq16 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq1107 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1075
       have i₂ := eq766 x y
       grind)
    | exact superpose eq766 eq1075
    | exact resolve eq1075 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq1075
  have eq1108 : False := by grind
  exact eq1108

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq19
    | exact resolve eq19 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq40
    | exact resolve eq40 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq40
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | exact resolve eq59 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq64
    | (have j0 := eq64 X0 X1
       grind)
    | exact resolve eq64 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq91 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66
    | (have j0 := eq66 (τ X0) X1
       grind)
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq212 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq199
  have eq218 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq212
    | (have j0 := eq212 X0 X1
       grind)
    | exact resolve eq212 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq212
  have eq222 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1
       have j1 := eq91 X1 X0
       grind)
    | (have r₁ := eq218 X1 X0
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq218 (M.op X1 X1) (M.op X0 X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq218 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq218
  have eq227 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq232 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq222 (σ X1) X0
       grind)
    | exact superpose eq222 eq15
    | (have j1 := eq222 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq241 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq227 (τ X0) X1
       grind)
    | exact superpose eq227 eq18
    | (have j1 := eq227 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq227
  have eq466 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq241 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq241
    | exact resolve eq241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq499 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq466
    | (have j0 := eq466 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq466 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq1064 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq232 x y
       grind)
    | exact superpose eq232 eq16
    | (have j1 := eq232 x y
       grind)
    | exact resolve eq16 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq1142 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1064
       have i₂ := eq499 x y
       grind)
    | exact superpose eq499 eq1064
    | (have j1 := eq499 (σ x) (σ y)
       grind)
    | (have r₁ := eq1064
       have r₂ := eq499 x y
       grind)
    | (have r₁ := eq1064
       have r₂ := eq499 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1064
       have r₂ := eq499 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1064 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq1064
  have eq1143 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1142
  have eq1147 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1143
       grind)
    | exact superpose eq1143 eq10
    | exact resolve eq10 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1190 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1147
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1147
    | exact resolve eq1147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1191 : x = y := by grind
  clear eq1190
  have eq1199 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1191
       grind)
    | exact superpose eq1191 eq16
    | exact resolve eq16 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1200 : False := by grind
  exact eq1200

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxx_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
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
  have eq66 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (σ X0) X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq23
    | exact resolve eq23 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq67 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq19
    | exact resolve eq19 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq68 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq67
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq69 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66
    | exact resolve eq66 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq68
    | exact resolve eq68 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq69
    | exact resolve eq69 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq69
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq10
    | exact resolve eq10 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq122 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq16
    | (have j1 := eq44 x y
       grind)
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq292 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (M.op (τ X0) X1) ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq46 X0 X1
       grind)
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq12
    | (have j0 := eq12 (τ X0) X1
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq12 X1 (τ X0)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (M.op (τ X0) X1) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq46 X0 X1
       grind)
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq12 X1 (τ X0)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 X2 : G, (M.op X2 (τ X0)) = (M.op X2 (M.op (M.op (τ X0) X1) X2)) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (τ X0) X1
       have i₂ := eq46 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 (τ X0)
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq9
    | (have j1 := eq46 X0 X1
       grind)
    | exact resolve eq9 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq297 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq298 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq292 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq301 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X2 X1) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq294 X0 X1 X2
       have i₂ := eq9 X2 X1 (τ X0)
       grind)
    | exact superpose eq9 eq294
    | (have j0 := eq294 X0 X1 X2
       grind)
    | exact resolve eq294 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq302 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 X1
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq298
    | (have j0 := eq298 X0 X1
       grind)
    | exact resolve eq298 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq298
  have eq368 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq122
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq122
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq122
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq122 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq368
  have eq3439 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq297 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq297
    | exact resolve eq297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq3531 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3439 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3439
    | (have j0 := eq3439 X0 X1
       grind)
    | exact resolve eq3439 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439
  have eq3572 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3531 X0 X1
       grind)
    | exact superpose eq3531 eq10
    | (have j1 := eq3531 X0 X1
       grind)
    | exact resolve eq10 eq3531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3531
  have eq3620 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3572 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3572
    | (have j0 := eq3572 X0 X1
       grind)
    | exact resolve eq3572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3572
  have eq3674 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3620 (σ X0) (σ X1)
       grind)
    | exact superpose eq3620 eq15
    | (have j1 := eq3620 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620
  have eq3717 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3674 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq3674
    | (have j0 := eq3674 X0 X1
       grind)
    | exact resolve eq3674 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674
  have eq3748 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3717 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3717
    | (have j0 := eq3717 X0 X1
       grind)
    | exact resolve eq3717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3717
  have eq3755 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq301
    | exact resolve eq301 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq3846 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3755 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3755
    | (have j0 := eq3755 X0 X1 X2
       grind)
    | exact resolve eq3755 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3755
  have eq3878 : ∀ X0 X1 X2 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3846 X0 X1 X2
       grind)
    | exact superpose eq3846 eq10
    | (have j1 := eq3846 X0 X1 X2
       grind)
    | exact resolve eq10 eq3846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3846
  have eq3926 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3878 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3878
    | (have j0 := eq3878 X0 X1 X2
       grind)
    | exact resolve eq3878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3878
  have eq4415 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq302 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq302
    | (have j0 := eq302 (M.op (σ X0) (σ X0)) (k X0 X1)
       grind)
    | exact resolve eq302 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq4503 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4415 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4415
    | (have j0 := eq4415 X0 X1
       grind)
    | exact resolve eq4415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4415
  have eq4512 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4503 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq4503
    | (have j0 := eq4503 X0 X1
       grind)
    | exact resolve eq4503 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq4503
  have eq4542 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq4512 X0 X1
       grind)
    | exact superpose eq4512 eq10
    | (have j1 := eq4512 X0 X1
       grind)
    | exact resolve eq10 eq4512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4512
  have eq4597 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4542 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq4542
    | (have j0 := eq4542 X0 X1
       grind)
    | exact resolve eq4542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4542
  have eq4674 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4597 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4597
  have eq4923 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq369
       grind)
    | exact superpose eq369 eq16
    | exact resolve eq16 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq4924 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq4923
       have r₂ := eq78 x
       grind)
    | exact resolve eq4923 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4923
  have eq33924 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq4924
       grind)
    | exact superpose eq4924 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4924
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4924
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4924
       grind)
    | exact resolve eq12 eq4924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33925 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) X1)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 x X0 y
       have i₂ := eq4924
       grind)
    | exact superpose eq4924 eq26
    | exact resolve eq26 eq4924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4924
  have eq33943 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by grind
  clear eq33924
  have eq33945 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq33925 X0 x
       have i₂ := eq26 x y X0 x
       grind)
    | exact superpose eq26 eq33925
    | exact resolve eq33925 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33925
  have eq59293 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq33943
       grind)
    | exact superpose eq33943 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq33943
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq33943
       grind)
    | exact resolve eq12 eq33943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33943
  have eq59317 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by grind
  clear eq59293
  have eq59328 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq59317
       have i₂ := eq78 y
       grind)
    | exact superpose eq78 eq59317
    | exact resolve eq59317 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59317
  have eq59337 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq59328
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq59328
    | exact resolve eq59328 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59328
  have eq63295 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq33945 X0
       grind)
    | exact superpose eq33945 eq12
    | (have j0 := eq12 (σ y) (σ x)
       have j1 := eq33945 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq33945 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq33945 X0
       grind)
    | exact resolve eq12 eq33945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33945
  have eq63319 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq63295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63295
  have eq63330 : ∀ X0 : G, (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq63319 X0
       have i₂ := eq78 y
       grind)
    | exact superpose eq78 eq63319
    | (have j0 := eq63319 X0
       grind)
    | exact resolve eq63319 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63319
  have eq63339 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq63330 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq63330
    | (have j0 := eq63330 X0
       grind)
    | exact resolve eq63330 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63330
  have eq159123 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3748 x y
       grind)
    | exact superpose eq3748 eq16
    | (have j1 := eq3748 x y
       grind)
    | exact resolve eq16 eq3748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748
  have eq160376 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq159123
       have i₂ := eq59337
       grind)
    | exact superpose eq59337 eq159123
    | exact resolve eq159123 eq59337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59337 eq159123
  have eq160397 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq160376
  have eq160399 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq160397
       have i₂ := eq63339 x
       grind)
    | exact superpose eq63339 eq160397
    | exact resolve eq160397 eq63339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63339 eq160397
  have eq160406 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq160399
  have eq160407 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq160406
  have eq161323 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq160407
       grind)
    | exact superpose eq160407 eq10
    | exact resolve eq10 eq160407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160407
  have eq161613 : x = y ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq161323
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq161323
    | exact resolve eq161323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161323
  have eq161616 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq161613
       grind)
    | exact superpose eq161613 eq16
    | exact resolve eq16 eq161613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161613
  have eq161617 : (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq161616
       have r₂ := eq78 x
       grind)
    | exact resolve eq161616 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161616
  have eq162727 : (k y x) = (τ (σ (M.op y y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq161617
       grind)
    | exact superpose eq161617 eq10
    | exact resolve eq10 eq161617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161617
  have eq163026 : (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq162727
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq162727
    | exact resolve eq162727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162727
  have eq163041 : ∀ X0 : G, x = y ∨ (M.op y x) = (M.op y y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq163026
       have i₂ := eq3926 y x X0
       grind)
    | exact superpose eq3926 eq163026
    | (have j1 := eq3926 x y y
       grind)
    | exact resolve eq163026 eq3926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3926 eq163026
  have eq167624 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq163041 X0
       grind)
    | exact superpose eq163041 eq16
    | (have j1 := eq163041 y
       grind)
    | exact resolve eq16 eq163041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163041
  have eq167627 : ∀ X0 : G, (M.op y x) = (M.op y y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq167624 y
       grind)
    | (have r₁ := eq167624 X0
       have r₂ := eq78 x
       grind)
    | exact resolve eq167624 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167624
  have eq168876 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have j0 := eq167627 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167627
  have eq168877 : (M.op y x) = (M.op y y) := by grind
  clear eq168876
  have eq168945 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 y X0 y
       have i₂ := eq168877
       grind)
    | exact superpose eq168877 eq26
    | exact resolve eq26 eq168877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168877
  have eq168976 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq168945 X0 x
       have i₂ := eq26 x x X0 y
       grind)
    | exact superpose eq26 eq168945
    | exact resolve eq168945 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168945
  have eq170183 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq4674 X0 y
       have i₂ := eq168976 X0
       grind)
    | exact superpose eq168976 eq4674
    | (have j0 := eq4674 X0 y
       grind)
    | (have r₁ := eq4674 x y
       have r₂ := eq168976 x
       grind)
    | (have r₁ := eq4674 y x
       have r₂ := eq168976 y
       grind)
    | exact resolve eq4674 eq168976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4674
  have eq193150 : x = y ∨ (k x y) = (M.op x x) := by
    first
    | (have j0 := eq170183 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170183
  have eq193167 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq193150
       grind)
    | exact superpose eq193150 eq16
    | exact resolve eq16 eq193150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193150
  have eq193183 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq193167
       have r₂ := eq78 x
       grind)
    | exact resolve eq193167 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193167
  have eq193192 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq193183
       grind)
    | exact superpose eq193183 eq122
    | exact resolve eq122 eq193183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq193183
  have eq193273 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq193192
       have i₂ := eq168976 x
       grind)
    | exact superpose eq168976 eq193192
    | exact resolve eq193192 eq168976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193192
  have eq193274 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq193273
  have eq193295 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (σ x) X0 (σ y)
       have i₂ := eq193274
       grind)
    | exact superpose eq193274 eq26
    | exact resolve eq26 eq193274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193274
  have eq193343 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq193295 X0 x
       have i₂ := eq26 x (σ y) X0 (σ x)
       grind)
    | exact superpose eq26 eq193295
    | exact resolve eq193295 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq193295
  have eq193969 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq193343 X0
       grind)
    | exact superpose eq193343 eq16
    | (have j1 := eq193343 X0
       grind)
    | exact resolve eq16 eq193343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193343
  have eq194290 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq193969 X0
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq193969
    | (have j0 := eq193969 X0
       grind)
    | exact resolve eq193969 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193969
  have eq194298 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq194290 X0
       have i₂ := eq168976 x
       grind)
    | exact superpose eq168976 eq194290
    | (have j0 := eq194290 X0
       grind)
    | exact resolve eq194290 eq168976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194290
  have eq194299 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq194298 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194298
  have eq195127 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq194299 (σ x)
       grind)
    | exact superpose eq194299 eq16
    | exact resolve eq16 eq194299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194299
  have eq195260 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq195127
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq195127
    | exact resolve eq195127 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq195127
  have eq195414 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq195260
       have i₂ := eq168976 x
       grind)
    | exact superpose eq168976 eq195260
    | exact resolve eq195260 eq168976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168976 eq195260
  have eq195415 : False := by grind
  exact eq195415
