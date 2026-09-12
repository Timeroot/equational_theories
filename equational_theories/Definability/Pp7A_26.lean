import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq116 (σ X0)
       grind)
    | exact superpose eq116 eq15
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq116 (τ X0)
       grind)
    | exact superpose eq116 eq31
    | exact resolve eq31 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq128 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq121 X0
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq121
    | exact resolve eq121 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq130 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq119
    | exact resolve eq119 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq119
  have eq147 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq61
    | exact resolve eq61 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       have i₂ := eq147 X0 X1
       grind)
    | exact superpose eq147 eq12
    | exact resolve eq12 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       have i₂ := eq147 X0 X1
       grind)
    | exact superpose eq147 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       grind)
    | exact resolve eq13 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq620 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq610 X0 X1
       have i₂ := eq130 (M.op X0 X0)
       grind)
    | exact superpose eq130 eq610
    | (have j0 := eq610 X0 X1
       grind)
    | exact resolve eq610 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq626 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq620 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | exact resolve eq620 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq627 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq626 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq629 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 X1
       have i₂ := eq130 (M.op X0 X0)
       grind)
    | exact superpose eq130 eq627
    | (have j0 := eq627 X0 X1
       grind)
    | exact resolve eq627 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq631 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq629 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq629
    | (have j0 := eq629 X0 X1
       grind)
    | exact resolve eq629 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq633 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq631 X0 X1
       have j1 := eq187 X0 X1
       grind)
    | (have r₁ := eq631 X0 X1
       have r₂ := eq187 X0 X1
       grind)
    | exact resolve eq631 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq631
  have eq646 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X0 X0) (M.op X1 (σ X0))
       have i₂ := eq633 X0 X1
       grind)
    | exact superpose eq633 eq28
    | exact resolve eq28 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq647 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq646 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq646
    | exact resolve eq646 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq685 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (τ (M.op X1 (σ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq647 (σ X0) X1
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq647
    | exact resolve eq647 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (τ (M.op X1 (σ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X0 X0) (τ (M.op X1 (σ (σ X0))))
       have i₂ := eq685 X0 X1
       grind)
    | exact superpose eq685 eq28
    | exact resolve eq28 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq685
  have eq976 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (τ (M.op X1 (σ (σ X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq974 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq974
    | exact resolve eq974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1892 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq1942 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1892 X0 X1
       have i₂ := eq130 X1
       grind)
    | exact superpose eq130 eq1892
    | (have j0 := eq1892 X0 X1
       grind)
    | exact resolve eq1892 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892
  have eq2003 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1942 X0 X1
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq1942
    | (have j0 := eq1942 X0 X1
       grind)
    | exact resolve eq1942 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq1942
  have eq3776 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2003 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2003
    | exact resolve eq2003 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003
  have eq4007 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3776 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq3776
    | (have j0 := eq3776 X0 X1
       grind)
    | exact resolve eq3776 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3776
  have eq4037 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq4007 X0 X1
       have j1 := eq153 X1 X0
       grind)
    | (have r₁ := eq4007 X1 (τ X1)
       have r₂ := eq153 (τ X1) X1
       grind)
    | (have r₁ := eq4007 X1 X0
       have r₂ := eq153 X0 X1
       grind)
    | exact resolve eq4007 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq4007
  have eq4053 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4037 X0 X1
       have i₂ := eq128 X0
       grind)
    | exact superpose eq128 eq4037
    | (have j0 := eq4037 X0 X1
       grind)
    | exact resolve eq4037 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4037
  have eq4063 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4053 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4053
    | (have j0 := eq4053 X0 X1
       grind)
    | exact resolve eq4053 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4053
  have eq4069 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4063 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4063
    | exact resolve eq4063 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4063
  have eq5299 : ∀ X0 X1 : G, (M.op (τ (M.op X0 (σ X1))) (M.op X1 X1)) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (τ (M.op X0 (σ X1))) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq647 X1 X0
       have i₂ := eq4069 (τ (M.op X0 (σ X1))) (M.op X1 X1)
       grind)
    | exact superpose eq4069 eq647
    | (have j1 := eq4069 (τ (M.op X0 (σ X1))) (M.op X1 X1)
       grind)
    | exact resolve eq647 eq4069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq5300 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq976 X1 X0
       have i₂ := eq4069 (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)
       grind)
    | exact superpose eq4069 eq976
    | (have j1 := eq4069 (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)
       grind)
    | exact resolve eq976 eq4069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976 eq4069
  have eq5393 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)) = X1 ∨ (M.op (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5300 X0 X1
       have i₂ := eq61 X1 X1 X1
       grind)
    | (have i₁ := eq5300 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq61 eq5300
    | (have j0 := eq5300 X0 X1
       grind)
    | exact resolve eq5300 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5300
  have eq5394 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5393 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5393
  have eq5395 : ∀ X0 X1 : G, (M.op (τ (M.op X0 (σ X1))) (M.op X1 X1)) = X1 ∨ (M.op (τ (M.op X0 (σ X1))) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5299 X0 X1
       have i₂ := eq61 X1 X1 X1
       grind)
    | (have i₁ := eq5299 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq61 eq5299
    | (have j0 := eq5299 X0 X1
       grind)
    | exact resolve eq5299 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5299
  have eq5396 : ∀ X0 X1 : G, (M.op (τ (M.op X0 (σ X1))) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5395
  have eq5476 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X1 (σ (τ X0)))) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5396 X1 (τ X0)
       have i₂ := eq128 X0
       grind)
    | exact superpose eq128 eq5396
    | exact resolve eq5396 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq5396
  have eq5513 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X1 X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5476 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5476
    | exact resolve eq5476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476
  have eq5779 : ∀ X0 X1 X2 : G, (τ (M.op X2 X0)) = (M.op (M.op X1 (τ (M.op X2 X0))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (τ (M.op X2 X0)) (τ (M.op X0 X0))
       have i₂ := eq5513 X0 X2
       grind)
    | exact superpose eq5513 eq61
    | exact resolve eq61 eq5513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq5513
  have eq6228 : ∀ X0 X1 X2 : G, (M.op (τ (τ (M.op X1 (σ (σ X0))))) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1) x
       have i₂ := eq5394 X0 X1
       grind)
    | exact superpose eq5394 eq62
    | exact resolve eq62 eq5394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq5394
  have eq6864 : ∀ X0 X2 X3 : G, (τ X0) = (M.op (M.op X3 (τ X0)) (τ (M.op X0 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq5779 (M.op X0 X2) x (τ (τ (M.op x (σ (σ X0)))))
       have i₂ := eq6228 X0 x X2
       grind)
    | exact superpose eq6228 eq5779
    | exact resolve eq5779 eq6228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6228
  have eq7084 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5779 X1 (M.op x (τ X0)) X0
       have i₂ := eq6864 X0 X1 x
       grind)
    | exact superpose eq6864 eq5779
    | exact resolve eq5779 eq6864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5779 eq6864
  have eq7175 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7084 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7084
    | exact resolve eq7084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7084
  have eq7577 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq7175 X0 X1
       grind)
    | exact superpose eq7175 eq11
    | exact resolve eq11 eq7175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7175
  have eq7969 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7577 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7577
    | exact resolve eq7577 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7577
  have eq8503 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7969 y x
       grind)
    | exact superpose eq7969 eq16
    | (have r₁ := eq16
       have r₂ := eq7969 y x
       grind)
    | exact resolve eq16 eq7969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7969
  have eq8658 : False := by grind
  exact eq8658

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  clear eq18
  have eq97 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq59 eq97
    | exact resolve eq97 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq141 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq141 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq141
    | exact resolve eq141 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq173 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq191 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq213 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191
    | (have j0 := eq191 X0 X1
       grind)
    | exact resolve eq191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq220 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq28
    | exact resolve eq28 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq225 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq36
    | exact resolve eq36 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1339 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq220 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq220
    | (have j0 := eq220 x
       grind)
    | exact resolve eq220 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq2024 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq225
    | (have j0 := eq225 (M.op x y)
       grind)
    | exact resolve eq225 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq2471 : ∀ X0 X1 : G, (σ (k X0 (k (M.op x y) (τ X1)))) = (k (σ X0) (k (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq173
    | (have j0 := eq173 (M.op x y) X1 X0
       grind)
    | exact resolve eq173 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq3713 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (τ (σ (M.op x y)))))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq2471 X0 sF1
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq2471
    | exact resolve eq2471 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq3831 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq37 eq3713
    | exact resolve eq3713 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713
  have eq3871 : ∀ X0 : G, (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq3831 X0
       have i₂ := eq100 sF0
       grind)
    | exact superpose eq100 eq3831
    | exact resolve eq3831 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831
  have eq5556 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq5557 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq5563 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5557
  have eq5564 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5556
  have eq5569 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5563 eq1339
    | exact resolve eq1339 eq5563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq5563
  have eq5572 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5564 eq2024
    | exact resolve eq2024 eq5564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024 eq5564
  have eq5573 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5569
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5569
    | exact resolve eq5569 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5569
  have eq5576 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5572
    | exact resolve eq5572 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5572
  have eq6028 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (τ X1)) (M.op X0 X2)) = X0 ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (τ X1) X0 X2
       have i₂ := eq213 X1 X0
       grind)
    | (have i₁ := eq53 X1 (τ X0) x
       have i₂ := eq213 X0 X1
       grind)
    | exact superpose eq213 eq53
    | (have j1 := eq213 X1 X0
       grind)
    | exact resolve eq53 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6036 : ∀ X0 : G, x = (M.op (M.op x (τ X0)) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (M.op x x) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq80 (τ X0)
       have i₂ := eq213 X0 x
       grind)
    | exact superpose eq213 eq80
    | (have j1 := eq213 X0 x
       grind)
    | exact resolve eq80 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6038 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (τ X0)) (M.op (σ x) (σ y))) ∨ (k X0 (σ (σ x))) = X0 ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq81 (τ X0)
       have i₂ := eq213 X0 sF2
       grind)
    | exact superpose eq213 eq81
    | (have j1 := eq213 X0 (σ x)
       grind)
    | exact resolve eq81 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq213
  have eq6129 : ∀ X0 : G, x = (M.op (M.op x (τ X0)) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (M.op x x) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6036 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6036
    | (have j0 := eq6036 X0
       grind)
    | exact resolve eq6036 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6036
  have eq241876 : ∀ X0 : G, (M.op x x) = (M.op x (τ X0)) ∨ (k X0 (σ x)) = X0 ∨ (M.op x x) = (M.op x (τ X0)) := by
    intro X0
    first
    | exact superpose eq6129 eq54
    | (have j1 := eq6129 X0
       grind)
    | exact resolve eq54 eq6129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6129
  have eq241882 : ∀ X0 : G, (M.op x x) = (M.op x (τ X0)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq241876 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241876
  have eq241894 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (k (τ X0) x) = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) x
       have i₂ := eq241882 X0
       grind)
    | exact superpose eq241882 eq12
    | (have j0 := eq12 x x
       have j1 := eq241882 X0
       grind)
    | (have r₁ := eq12 (τ X0) x
       have r₂ := eq241882 X0
       grind)
    | exact resolve eq12 eq241882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241882
  have eq241906 : ∀ X0 : G, (k (τ X0) x) = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq241894 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241894
  have eq242030 : ∀ X0 : G, (k X0 x) = (M.op x x) ∨ (σ X0) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq241906 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq241906
    | (have j0 := eq241906 (σ X0)
       grind)
    | exact resolve eq241906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241906
  have eq242115 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30 eq242030
    | (have j0 := eq242030 X0
       grind)
    | exact resolve eq242030 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242030
  have eq243944 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 x)
       have i₂ := eq242115 X0
       grind)
    | exact superpose eq242115 eq10
    | (have j1 := eq242115 X0
       grind)
    | exact resolve eq10 eq242115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243949 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k (k X0 x) x)) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq30 (k X0 x)
       have i₂ := eq242115 X0
       grind)
    | exact superpose eq242115 eq30
    | (have j1 := eq242115 X0
       grind)
    | exact resolve eq30 eq242115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242115
  have eq243997 : ∀ X0 : G, (σ (k X0 x)) = (σ (k (k X0 x) x)) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30 eq243949
    | (have j0 := eq243949 X0
       grind)
    | exact resolve eq243949 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq243949
  have eq244002 : ∀ X0 : G, (k X0 x) = X0 ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq243944 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq243944
    | (have j0 := eq243944 X0
       grind)
    | exact resolve eq243944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243944
  have eq244170 : ∀ X0 : G, (M.op x x) ≠ X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq244002 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244002
  have eq263815 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) ∨ (k X0 (σ (σ x))) = X0 ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) := by
    intro X0
    first
    | exact superpose eq6038 eq54
    | (have j1 := eq6038 X0
       grind)
    | exact resolve eq54 eq6038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6038
  have eq263820 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) ∨ (k X0 (σ (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq263815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263815
  have eq263835 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ X0) = (k (σ X0) (σ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq263820 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq263820
    | (have j0 := eq263820 (σ X0)
       grind)
    | exact resolve eq263820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263820
  have eq263860 : ∀ X0 : G, (σ X0) = (σ (k X0 (σ x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq263835 X0
       have i₂ := eq15 X0 sF2
       grind)
    | exact superpose eq15 eq263835
    | (have j0 := eq263835 X0
       grind)
    | exact resolve eq263835 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263835
  have eq264159 : ∀ X0 : G, (τ (σ X0)) = (k X0 (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq263860 eq10
    | (have j1 := eq263860 X0
       grind)
    | exact resolve eq10 eq263860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263860
  have eq264221 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq264159 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq264159
    | (have j0 := eq264159 X0
       grind)
    | exact resolve eq264159 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264159
  have eq264292 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq264221 eq59
    | (have j1 := eq264221 (σ y)
       grind)
    | exact resolve eq59 eq264221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq264221
  have eq264474 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq264292
    | exact resolve eq264292 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264292
  have eq264597 : (τ (σ y)) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq264474
       grind)
    | exact superpose eq264474 eq10
    | exact resolve eq10 eq264474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264622 : (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (k y x) (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3871 (k y x)
       have i₂ := eq264474
       grind)
    | exact superpose eq264474 eq3871
    | exact resolve eq3871 eq264474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871 eq264474
  have eq264633 : (σ (M.op x y)) = (σ (k (k y x) (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5576 eq264622
    | exact resolve eq264622 eq5576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264622
  have eq264654 : y = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq39 eq264597
    | exact resolve eq264597 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264597
  have eq265491 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (k y x) (M.op (M.op x y) (M.op x y))) (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq264633 eq29
    | exact resolve eq29 eq264633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq264633
  have eq265503 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (k y x) (M.op (M.op x y) (M.op x y))) (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq265491
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq265491
    | exact resolve eq265491 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265491
  have eq440570 : ∀ X0 : G, (τ (σ (k X0 x))) = (k (k X0 x) x) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 x) x)
       have i₂ := eq243997 X0
       grind)
    | exact superpose eq243997 eq10
    | (have j1 := eq243997 X0
       grind)
    | exact resolve eq10 eq243997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243997
  have eq440583 : ∀ X0 : G, (k X0 x) = (k (k X0 x) x) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq440570 X0
       have i₂ := eq10 (k X0 x)
       grind)
    | exact superpose eq10 eq440570
    | (have j0 := eq440570 X0
       grind)
    | exact resolve eq440570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440570
  have eq440590 : ∀ X0 : G, (k X0 x) = (k (k X0 x) x) := by
    intro X0
    first
    | (have j0 := eq440583 X0
       have j1 := eq244170 (k X0 x)
       grind)
    | (have r₁ := eq440583 X0
       have r₂ := eq244170 (k X0 x)
       grind)
    | exact resolve eq440583 eq244170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244170 eq440583
  have eq452877 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (τ X1) (M.op X0 x)
       have i₂ := eq6028 X0 X1 x
       grind)
    | exact superpose eq6028 eq54
    | (have j1 := eq6028 X0 X1 x
       grind)
    | exact resolve eq54 eq6028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq6028
  have eq453546 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq452877 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452877
  have eq454831 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq453546 X1 (σ X0)
       grind)
    | exact superpose eq453546 eq15
    | (have j1 := eq453546 X1 (σ X0)
       grind)
    | exact resolve eq15 eq453546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453546
  have eq454876 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq454831 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq454831
    | (have j0 := eq454831 X0 X1
       grind)
    | exact resolve eq454831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454831
  have eq465731 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq454876 X0 X1
       grind)
    | exact superpose eq454876 eq10
    | (have j1 := eq454876 X0 X1
       grind)
    | exact resolve eq10 eq454876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454876
  have eq465788 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq465731 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq465731
    | (have j0 := eq465731 X0 X1
       grind)
    | exact resolve eq465731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465731
  have eq466022 : (σ (M.op x y)) = (σ x) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5573
       have i₂ := eq465788 sF1 (M.op sF2 sF2)
       grind)
    | exact superpose eq465788 eq5573
    | (have j1 := eq465788 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq5573 eq465788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5573
  have eq466026 : (σ (M.op x y)) = (σ y) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq5576
       have i₂ := eq465788 sF3 (M.op sF1 sF1)
       grind)
    | exact superpose eq465788 eq5576
    | (have j1 := eq465788 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq5576 eq465788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465788
  have eq466784 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq466026
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq466026
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq466026
    | exact resolve eq466026 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466026
  have eq466788 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq466022
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq466022
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq466022
    | exact resolve eq466022 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq466022
  have eq466900 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq466784 eq82
    | exact resolve eq82 eq466784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466784
  have eq466989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq466788 eq466900
    | exact resolve eq466900 eq466788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466900
  have eq467011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq466989
    | exact resolve eq466989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466989
  have eq467015 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq467011
       have r₂ := eq27
       grind)
    | exact resolve eq467011 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467011
  have eq467020 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq467015 eq39
    | exact resolve eq39 eq467015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq467015
  have eq467344 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq467020
    | exact resolve eq467020 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467020
  have eq467352 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq467344 eq38
    | exact resolve eq38 eq467344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467358 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq467344 eq104
    | exact resolve eq104 eq467344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467344
  have eq467962 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq467352
    | exact resolve eq467352 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467352
  have eq467966 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq467962 eq20
    | exact resolve eq20 eq467962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467967 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq467962 eq77
    | exact resolve eq77 eq467962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq468689 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq468709 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq467966
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq467966
    | exact resolve eq467966 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467966
  have eq473939 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq467967 (M.op y x)
       have i₂ := eq467967 x
       grind)
    | exact superpose eq467967 eq467967
    | exact resolve eq467967 eq467967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467967
  have eq473973 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq473939
  have eq474017 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142 y
       have i₂ := eq473973
       grind)
    | exact superpose eq473973 eq142
    | exact resolve eq142 eq473973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473973
  have eq474150 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq474017
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq474017
    | exact resolve eq474017 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474017
  have eq474210 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq468709 eq474150
    | exact resolve eq474150 eq468709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468709 eq474150
  have eq474328 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq474210
  have eq474481 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq474328 eq5576
    | exact resolve eq5576 eq474328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5576 eq474328
  have eq474659 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq474481
    | exact resolve eq474481 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq474481
  have eq475109 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq467962 eq474659
    | exact resolve eq474659 eq467962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467962 eq474659
  have eq475609 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq475109
       have r₂ := eq468689
       grind)
    | exact resolve eq475109 eq468689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468689 eq475109
  have eq475627 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq475609
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq475609
    | exact resolve eq475609 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq475609
  have eq475631 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq475627
       have i₂ := eq142 y
       grind)
    | exact superpose eq142 eq475627
    | exact resolve eq475627 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq475627
  have eq475634 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq475631
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq475631
    | exact resolve eq475631 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475631
  have eq475740 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq475634 eq82
    | exact resolve eq82 eq475634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq475634
  have eq500109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq466788 eq475740
    | exact resolve eq475740 eq466788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466788 eq475740
  have eq500169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq500109
    | exact resolve eq500109 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500109
  have eq500173 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq500169
       have r₂ := eq27
       grind)
    | exact resolve eq500169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500169
  have eq500178 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq500173 eq38
    | exact resolve eq38 eq500173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq500173
  have eq500795 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq500178
    | exact resolve eq500178 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq500178
  have eq500796 : x = (M.op x y) := by grind
  clear eq500795
  have eq500801 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq500796 eq20
    | exact resolve eq20 eq500796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq500810 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq500796 eq80
    | exact resolve eq80 eq500796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq500813 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq500796 eq95
    | exact resolve eq95 eq500796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq520517 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (k y x) (M.op x x)) x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq500796 eq265503
    | exact resolve eq265503 eq500796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265503
  have eq523542 : x = y ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq500796 eq467358
    | exact resolve eq467358 eq500796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467358
  have eq526831 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq500796 eq500813
    | exact resolve eq500813 eq500796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500796 eq500813
  have eq526834 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq500801
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq500801
    | exact resolve eq500801 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500801
  have eq527928 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq526834 eq22
    | exact resolve eq22 eq526834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq527929 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq526834 eq26
    | exact resolve eq26 eq526834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq527937 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq526834 eq104
    | exact resolve eq104 eq526834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq534795 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k y x) := by
    first
    | exact superpose eq526834 eq264654
    | exact resolve eq264654 eq526834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264654
  have eq537870 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (k y x) (M.op x x)) x)) := by
    first
    | exact superpose eq526834 eq520517
    | exact resolve eq520517 eq526834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520517 eq526834
  have eq544828 : x = (M.op x x) := by
    first
    | (have i₁ := eq500810 (M.op x x)
       have i₂ := eq500810 x
       grind)
    | exact superpose eq500810 eq500810
    | exact resolve eq500810 eq500810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500810
  have eq546762 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq526831
       have i₂ := eq544828
       grind)
    | exact superpose eq544828 eq526831
    | (have r₁ := eq526831
       have r₂ := eq544828
       grind)
    | exact resolve eq526831 eq544828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526831
  have eq546954 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (k y x) x) x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq537870
       have i₂ := eq544828
       grind)
    | exact superpose eq544828 eq537870
    | exact resolve eq537870 eq544828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537870 eq544828
  have eq547254 : x = (k y x) := by grind
  clear eq546762
  have eq547284 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k y x) x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq546954
       have i₂ := eq440590 (k y x)
       grind)
    | exact superpose eq440590 eq546954
    | exact resolve eq546954 eq440590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546954
  have eq547376 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq523542
       have i₂ := eq547254
       grind)
    | exact superpose eq547254 eq523542
    | exact resolve eq523542 eq547254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523542
  have eq547415 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq527937
       have i₂ := eq547254
       grind)
    | exact superpose eq547254 eq527937
    | exact resolve eq527937 eq547254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527937
  have eq547438 : x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq534795
       have i₂ := eq547254
       grind)
    | exact superpose eq547254 eq534795
    | exact resolve eq534795 eq547254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534795
  have eq547857 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq547284
       have i₂ := eq440590 y
       grind)
    | exact superpose eq440590 eq547284
    | exact resolve eq547284 eq440590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440590 eq547284
  have eq548004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq547415
       have i₂ := eq527928
       grind)
    | exact superpose eq527928 eq547415
    | exact resolve eq547415 eq527928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547415
  have eq548032 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq547376
       have r₂ := eq547438
       grind)
    | exact resolve eq547376 eq547438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547376 eq547438
  have eq548143 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq547857
       have i₂ := eq547254
       grind)
    | exact superpose eq547254 eq547857
    | exact resolve eq547857 eq547254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547254 eq547857
  have eq548183 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq548004
       have r₂ := eq27
       grind)
    | exact resolve eq548004 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548004
  have eq548190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq548032
       have i₂ := eq527928
       grind)
    | exact superpose eq527928 eq548032
    | exact resolve eq548032 eq527928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548032
  have eq548218 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq548143
       have i₂ := eq527928
       grind)
    | exact superpose eq527928 eq548143
    | exact resolve eq548143 eq527928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548143
  have eq548252 : x = y := by
    first
    | (have r₁ := eq548190
       have r₂ := eq27
       grind)
    | exact resolve eq548190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548190
  have eq548268 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq548218
       have r₂ := eq548183
       grind)
    | exact resolve eq548218 eq548183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548183 eq548218
  have eq548287 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq548252
       grind)
    | exact superpose eq548252 eq24
    | exact resolve eq24 eq548252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq548252
  have eq561262 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq548287
       have i₂ := eq527928
       grind)
    | exact superpose eq527928 eq548287
    | exact resolve eq548287 eq527928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527928 eq548287
  have eq561895 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq561262 eq527929
    | exact resolve eq527929 eq561262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527929 eq561262
  have eq566792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq548268 eq561895
    | exact resolve eq561895 eq548268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548268 eq561895
  have eq567559 : False := by grind
  exact eq567559

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) ≠ X0 ∨ (k (M.op X0 X3) (M.op (M.op X1 X2) X0)) = (M.op (M.op X0 X3) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X3) (M.op (M.op X1 X2) X0)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X3) (M.op (M.op X1 X2) X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : y ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ y = (k x y) := by
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
  have eq82 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq97 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq70 sF3
       grind)
    | exact superpose eq70 eq96
    | exact resolve eq96 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq100 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq98
    | exact resolve eq98 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq89 x y
       grind)
    | exact superpose eq89 eq44
    | (have j1 := eq89 x y
       grind)
    | exact resolve eq44 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq131 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq128
    | exact resolve eq128 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq132 eq89
    | (have j0 := eq89 (σ x) (σ y)
       grind)
    | exact resolve eq89 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq199
    | exact resolve eq199 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq203 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq200
       have r₂ := eq27
       grind)
    | exact resolve eq200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq203
    | exact resolve eq203 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq207 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq205 eq27
    | exact resolve eq27 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq89 (σ X0) sF3
       grind)
    | exact superpose eq89 eq40
    | (have j1 := eq89 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq89
  have eq320 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq333 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq622 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq205 eq82
    | (have r₁ := eq82
       have r₂ := eq205
       grind)
    | exact resolve eq82 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq623 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq622
  have eq1489 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq205 eq321
    | exact resolve eq321 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq321
  have eq1509 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1489 eq1489
    | exact resolve eq1489 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1517 : (σ y) = (M.op (M.op (M.op x y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1489 eq50
    | exact resolve eq50 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1489
  have eq1531 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1509
  have eq1679 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ y) X0) (σ y)) = (k (M.op (σ y) X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1517 eq68
    | exact resolve eq68 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1517
  have eq1698 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (k (M.op (σ y) X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1679 X0
       grind)
    | (have r₁ := eq1679 X0
       have r₂ := eq1531
       grind)
    | exact resolve eq1679 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679
  have eq4614 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq623 eq1531
    | exact resolve eq1531 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq1531
  have eq4653 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq4614
  have eq4659 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq4653 eq132
    | exact resolve eq132 eq4653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653
  have eq4663 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq4659
  have eq4668 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4663
       have r₂ := eq207
       grind)
    | exact resolve eq4663 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq4663
  have eq4679 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4668 eq333
    | exact resolve eq333 eq4668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq4668
  have eq4719 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4679 eq1698
    | exact resolve eq1698 eq4679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698 eq4679
  have eq4750 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4719
  have eq4754 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq4750
    | exact resolve eq4750 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4750
  have eq5090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4754 eq132
    | exact resolve eq132 eq4754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq4754
  have eq5093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5090
  have eq5098 : y = (M.op x y) := by
    first
    | (have r₁ := eq5093
       have r₂ := eq27
       grind)
    | exact resolve eq5093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5093
  have eq5101 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5098 eq20
    | exact resolve eq20 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq5105 : y ≠ y ∨ (M.op y x) = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq5098 eq81
    | (have r₁ := eq81
       have r₂ := eq5098
       grind)
    | exact resolve eq81 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq5116 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq5098 eq320
    | exact resolve eq320 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq5117 : ∀ X0 : G, x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | exact superpose eq5098 eq332
    | exact resolve eq332 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq5119 : (M.op y x) = (M.op y y) ∨ y = (k x y) := by grind
  clear eq5105
  have eq5125 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5101
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5101
    | exact resolve eq5101 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101
  have eq5129 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq5125 eq26
    | exact resolve eq26 eq5125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq5257 : y = (M.op y y) := by
    first
    | (have i₁ := eq5116 (M.op y x)
       have i₂ := eq5116 x
       grind)
    | exact superpose eq5116 eq5116
    | exact resolve eq5116 eq5116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5116
  have eq5283 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq5257
       grind)
    | exact superpose eq5257 eq100
    | exact resolve eq100 eq5257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq5316 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5125 eq5283
    | exact resolve eq5283 eq5125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5283
  have eq5319 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5316
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5316
    | exact resolve eq5316 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5316
  have eq5320 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5125 eq5319
    | exact resolve eq5319 eq5125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319
  have eq6452 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq5125 eq222
    | (have j0 := eq222 X0
       grind)
    | exact resolve eq222 eq5125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq6453 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5125 eq6452
    | (have j0 := eq6452 X0
       grind)
    | exact resolve eq6452 eq5125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6452
  have eq6476 : (σ (k x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6453 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6453
    | (have j0 := eq6453 x
       grind)
    | exact resolve eq6453 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6453
  have eq6502 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq5129 eq6476
    | exact resolve eq6476 eq5129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6476
  have eq6517 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6502
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6502
    | exact resolve eq6502 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq6502
  have eq6527 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq5125 eq6517
    | exact resolve eq6517 eq5125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6517
  have eq6535 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq5129 eq6527
    | exact resolve eq6527 eq5129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5129 eq6527
  have eq6540 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq6535
       have r₂ := eq27
       grind)
    | exact resolve eq6535 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq6554 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6540 eq64
    | exact resolve eq64 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq6556 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5098 eq6554
    | exact resolve eq6554 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5098 eq6554
  have eq7184 : y = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq5119
       have i₂ := eq5257
       grind)
    | exact superpose eq5257 eq5119
    | exact resolve eq5119 eq5257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5119
  have eq7185 : y = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7184
       have i₂ := eq6556
       grind)
    | exact superpose eq6556 eq7184
    | exact resolve eq7184 eq6556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6556 eq7184
  have eq7193 : x = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5117 y
       have i₂ := eq7185
       grind)
    | exact superpose eq7185 eq5117
    | exact resolve eq5117 eq7185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5117 eq7185
  have eq7220 : y = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq7193
       have i₂ := eq5257
       grind)
    | exact superpose eq5257 eq7193
    | exact resolve eq7193 eq5257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5257 eq7193
  have eq7228 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq7220 eq15
    | exact resolve eq15 eq7220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7220
  have eq7241 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq7228
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7228
    | exact resolve eq7228 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7228
  have eq7243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5125 eq7241
    | exact resolve eq7241 eq5125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7241
  have eq7245 : x = y := by
    first
    | (have r₁ := eq7243
       have r₂ := eq27
       grind)
    | exact resolve eq7243 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7243
  have eq7250 : (σ (k x (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq97
       have i₂ := eq7245
       grind)
    | exact superpose eq7245 eq97
    | exact resolve eq97 eq7245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq7245
  have eq7309 : (σ (k x (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5125 eq7250
    | exact resolve eq7250 eq5125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5125 eq7250
  have eq7323 : (σ (k x (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7309
       have i₂ := eq70 sF1
       grind)
    | exact superpose eq70 eq7309
    | exact resolve eq7309 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq7309
  have eq7336 : (σ (M.op x y)) = (σ (k x (M.op x y))) := by
    first
    | exact superpose eq5320 eq7323
    | exact resolve eq7323 eq5320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5320 eq7323
  have eq7342 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq45 eq7336
    | exact resolve eq7336 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq7336
  have eq7344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6540 eq7342
    | exact resolve eq7342 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6540 eq7342
  have eq7345 : False := by grind
  exact eq7345

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq39
    | exact resolve eq39 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq39
  have eq58 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq74 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (σ X0) (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq19
    | exact resolve eq19 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq19
    | exact resolve eq19 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq251 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq273 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq251
    | (have j0 := eq251 X0 X1
       grind)
    | exact resolve eq251 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq279 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq273 X1 X0
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq273 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq880 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq279
    | exact resolve eq279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq279 (σ X1) X0
       grind)
    | exact superpose eq279 eq15
    | (have j1 := eq279 (σ X1) X0
       grind)
    | exact resolve eq15 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq940 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq880 X0 (τ X1)
       grind)
    | exact superpose eq880 eq17
    | (have j1 := eq880 X0 (τ X1)
       grind)
    | exact resolve eq17 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq3389 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq940 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq940
    | exact resolve eq940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq3502 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3389 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3389
    | (have j0 := eq3389 X0 X1
       grind)
    | exact resolve eq3389 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389
  have eq5504 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq896 x y
       grind)
    | exact superpose eq896 eq16
    | (have j1 := eq896 x y
       grind)
    | exact resolve eq16 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5597 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq896 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq5752 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5597 (τ X1) (τ X0)
       have i₂ := eq58 X1 X0
       grind)
    | exact superpose eq58 eq5597
    | (have j0 := eq5597 (τ X1) (τ X0)
       grind)
    | exact resolve eq5597 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq5597
  have eq5760 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5752 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5752
    | (have j0 := eq5752 X0 X1
       grind)
    | exact resolve eq5752 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5752
  have eq5777 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5760 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5760
    | (have j0 := eq5760 X0 X1
       grind)
    | exact resolve eq5760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5760
  have eq5788 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5777 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5777
    | (have j0 := eq5777 X0 X1
       grind)
    | exact resolve eq5777 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5777
  have eq5795 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5788 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5788
    | (have j0 := eq5788 X0 X1
       grind)
    | exact resolve eq5788 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5788
  have eq6542 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5504
       have i₂ := eq3502 y x
       grind)
    | exact superpose eq3502 eq5504
    | (have j1 := eq3502 (σ y) (σ x)
       grind)
    | (have r₁ := eq5504
       have r₂ := eq3502 y x
       grind)
    | exact resolve eq5504 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3502
  have eq6543 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6542
  have eq6743 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 x y
       have i₂ := eq6543
       grind)
    | exact superpose eq6543 eq19
    | exact resolve eq19 eq6543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6543
  have eq6762 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6743 (M.op x x)
       have i₂ := eq6743 x
       grind)
    | exact superpose eq6743 eq6743
    | exact resolve eq6743 eq6743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6743
  have eq6792 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq6762
  have eq7023 : (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75 x (σ y)
       have i₂ := eq6792
       grind)
    | exact superpose eq6792 eq75
    | exact resolve eq75 eq6792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq7030 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ x) (σ y)
       have i₂ := eq6792
       grind)
    | exact superpose eq6792 eq19
    | exact resolve eq19 eq6792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6792
  have eq8609 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74 x (σ (M.op x x))
       have i₂ := eq7023
       grind)
    | exact superpose eq7023 eq74
    | exact resolve eq74 eq7023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq9330 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7030 (σ (M.op x x))
       have i₂ := eq7023
       grind)
    | exact superpose eq7023 eq7030
    | exact resolve eq7030 eq7023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7023 eq7030
  have eq9363 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq9330
  have eq9372 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9363
       have i₂ := eq42 x
       grind)
    | exact superpose eq42 eq9363
    | exact resolve eq9363 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq9363
  have eq10760 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ (M.op x x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq78 x (σ (M.op x x))
       have i₂ := eq8609
       grind)
    | exact superpose eq8609 eq78
    | exact resolve eq78 eq8609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8609
  have eq10801 : (σ x) = (k (σ (M.op x x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10760
       have r₂ := eq9372
       grind)
    | exact resolve eq10760 eq9372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9372 eq10760
  have eq10809 : (σ x) = (σ (k (M.op x x) x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10801
       have i₂ := eq15 (M.op x x) x
       grind)
    | exact superpose eq15 eq10801
    | exact resolve eq10801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10801
  have eq10871 : (τ (σ x)) = (k (M.op x x) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (k (M.op x x) x)
       have i₂ := eq10809
       grind)
    | exact superpose eq10809 eq10
    | exact resolve eq10 eq10809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10809
  have eq10951 : x = (k (M.op x x) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10871
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10871
    | exact resolve eq10871 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10871
  have eq10967 : x ≠ x ∨ x = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5795 (M.op x x) x
       have i₂ := eq10951
       grind)
    | exact superpose eq10951 eq5795
    | (have j0 := eq5795 (M.op x x) x
       grind)
    | (have r₁ := eq5795 (M.op x x) x
       have r₂ := eq10951
       grind)
    | exact resolve eq5795 eq10951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5795 eq10951
  have eq10970 : x = (M.op x (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq10967
  have eq11151 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq19 X0 x (M.op x x)
       have i₂ := eq10970
       grind)
    | exact superpose eq10970 eq19
    | exact resolve eq19 eq10970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq10970
  have eq11174 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11151 (M.op x x)
       have i₂ := eq11151 x
       grind)
    | exact superpose eq11151 eq11151
    | exact resolve eq11151 eq11151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11151
  have eq11214 : x = (M.op x x) := by grind
  clear eq11174
  have eq11394 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq36 x x
       have i₂ := eq11214
       grind)
    | exact superpose eq11214 eq36
    | exact resolve eq36 eq11214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq11468 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq11394 X0
       have j1 := eq880 x X0
       grind)
    | (have r₁ := eq11394 x
       have r₂ := eq880 x x
       grind)
    | exact resolve eq11394 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq11394
  have eq11893 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5504
       have i₂ := eq11468 y
       grind)
    | exact superpose eq11468 eq5504
    | exact resolve eq5504 eq11468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504
  have eq11896 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11893
  have eq11930 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11896
       grind)
    | exact superpose eq11896 eq16
    | exact resolve eq16 eq11896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11933 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq78 x (σ y)
       have i₂ := eq11896
       grind)
    | exact superpose eq11896 eq78
    | exact resolve eq78 eq11896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq11896
  have eq11971 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11933
       have i₂ := eq11214
       grind)
    | exact superpose eq11214 eq11933
    | exact resolve eq11933 eq11214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11214 eq11933
  have eq11972 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq11971
  have eq11986 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11972
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq11972
    | exact resolve eq11972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11972
  have eq11997 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11986
       have i₂ := eq11468 y
       grind)
    | exact superpose eq11468 eq11986
    | exact resolve eq11986 eq11468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11468 eq11986
  have eq12003 : False := by grind
  exact eq12003

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq115 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq116 (σ X0)
       grind)
    | exact superpose eq116 eq15
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq119
    | exact resolve eq119 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq119
  have eq153 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2045 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq2108 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2045 X0 X1
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq2045
    | (have j0 := eq2045 X0 X1
       grind)
    | exact resolve eq2045 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq3991 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2108 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2108
    | exact resolve eq2108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108
  have eq4144 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3991 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq3991
    | (have j0 := eq3991 X0 X1
       grind)
    | exact resolve eq3991 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991
  have eq4171 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq4144 X0 X1
       have j1 := eq153 X1 X0
       grind)
    | (have r₁ := eq4144 X1 X0
       have r₂ := eq153 X0 X1
       grind)
    | exact resolve eq4144 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144
  have eq4218 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4171 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4171
    | exact resolve eq4171 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4256 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4171 (σ X1) X0
       grind)
    | exact superpose eq4171 eq15
    | (have j1 := eq4171 (σ X1) X0
       grind)
    | exact resolve eq15 eq4171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4171
  have eq4383 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq4218 X0 (τ X1)
       grind)
    | exact superpose eq4218 eq17
    | (have j1 := eq4218 X0 (τ X1)
       grind)
    | exact resolve eq17 eq4218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq4724 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4383 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4383
    | exact resolve eq4383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4383
  have eq4891 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4724 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4724
    | (have j0 := eq4724 X0 X1
       grind)
    | exact resolve eq4724 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724
  have eq6725 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4256 x y
       grind)
    | exact superpose eq4256 eq16
    | (have j1 := eq4256 x y
       grind)
    | exact resolve eq16 eq4256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4256
  have eq7531 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6725
       have i₂ := eq4891 y x
       grind)
    | exact superpose eq4891 eq6725
    | (have j1 := eq4891 (σ y) (σ x)
       grind)
    | (have r₁ := eq6725
       have r₂ := eq4891 y x
       grind)
    | exact resolve eq6725 eq4891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4891
  have eq7532 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7531
  have eq7539 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 x y
       have i₂ := eq7532
       grind)
    | exact superpose eq7532 eq61
    | exact resolve eq61 eq7532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7532
  have eq7554 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7539 (M.op x x)
       have i₂ := eq7539 x
       grind)
    | exact superpose eq7539 eq7539
    | exact resolve eq7539 eq7539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7539
  have eq7579 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq7554
  have eq7594 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq7579
       grind)
    | exact superpose eq7579 eq61
    | exact resolve eq61 eq7579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq7579
  have eq8096 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7594 (M.op x (σ x))
       have i₂ := eq7594 x
       grind)
    | exact superpose eq7594 eq7594
    | exact resolve eq7594 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7594
  have eq8128 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq8096
  have eq8136 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8128
       have i₂ := eq130 x
       grind)
    | exact superpose eq130 eq8128
    | exact resolve eq8128 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq8128
  have eq8171 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq8136
       grind)
    | exact superpose eq8136 eq10
    | exact resolve eq10 eq8136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8136
  have eq8275 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8171
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8171
    | exact resolve eq8171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8171
  have eq8276 : x = (M.op x x) := by grind
  clear eq8275
  have eq8288 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq115 x x
       have i₂ := eq8276
       grind)
    | exact superpose eq8276 eq115
    | exact resolve eq115 eq8276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq8388 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq8288 X0
       have j1 := eq4218 x X0
       grind)
    | (have r₁ := eq8288 x
       have r₂ := eq4218 x x
       grind)
    | exact resolve eq8288 eq4218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4218 eq8288
  have eq8522 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6725
       have i₂ := eq8388 y
       grind)
    | exact superpose eq8388 eq6725
    | exact resolve eq6725 eq8388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6725
  have eq8523 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8522
  have eq8546 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8523
       grind)
    | exact superpose eq8523 eq16
    | exact resolve eq16 eq8523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8547 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq153 x (σ y)
       have i₂ := eq8523
       grind)
    | exact superpose eq8523 eq153
    | exact resolve eq153 eq8523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq8523
  have eq8586 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8547
       have i₂ := eq8276
       grind)
    | exact superpose eq8276 eq8547
    | exact resolve eq8547 eq8276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8276 eq8547
  have eq8587 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq8586
  have eq8600 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq8587
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8587
    | exact resolve eq8587 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8587
  have eq8609 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8600
       have i₂ := eq8388 y
       grind)
    | exact superpose eq8388 eq8600
    | exact resolve eq8600 eq8388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8388 eq8600
  have eq8615 : False := by grind
  exact eq8615

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyy_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  clear eq24
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by
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
  have eq67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq43
    | exact resolve eq43 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq49
    | exact resolve eq49 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq74
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq74
    | exact resolve eq74 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq73
    | exact resolve eq73 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq97 : (σ (k y (k x x))) = (k (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq36
    | exact resolve eq36 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq100 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq106 : (k (σ y) (M.op (σ x) (σ x))) = (σ (k y (k x x))) := by
    first
    | (have i₁ := eq97
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq97
    | exact resolve eq97 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq108 : (σ (k y (M.op x x))) = (k (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq106
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq106
    | exact resolve eq106 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq150 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq153 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq150
       have i₂ := eq70 sF1
       grind)
    | exact superpose eq70 eq150
    | exact resolve eq150 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq155 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq153
       have i₂ := eq70 sF0
       grind)
    | exact superpose eq70 eq153
    | exact resolve eq153 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq153
  have eq172 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq155 eq36
    | exact resolve eq36 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq155
  have eq241 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq50 eq13
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq281 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq291 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq281 eq52
    | exact resolve eq52 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq281
  have eq1450 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq321 eq250
    | (have j0 := eq250 y
       grind)
    | (have r₁ := eq250 y
       have r₂ := eq321 (M.op x y)
       grind)
    | exact resolve eq250 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq321
  have eq1452 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq1450
  have eq2725 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1452 eq172
    | exact resolve eq172 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq1452
  have eq2726 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq2725
    | exact resolve eq2725 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq9064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq9064
    | exact resolve eq9064 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9064
  have eq9076 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq9065
       have r₂ := eq27
       grind)
    | exact resolve eq9065 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9065
  have eq9080 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq9076
    | exact resolve eq9076 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9076
  have eq9082 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq9080
    | exact resolve eq9080 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9080
  have eq9084 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq9082 eq67
    | (have r₁ := eq67
       have r₂ := eq9082
       grind)
    | exact resolve eq67 eq9082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9082
  have eq9137 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq9084
  have eq9220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq9137 eq118
    | exact resolve eq118 eq9137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9137
  have eq9228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9220
  have eq9230 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9228
       have r₂ := eq27
       grind)
    | exact resolve eq9228 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9228
  have eq9232 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq9230
       grind)
    | exact superpose eq9230 eq66
    | (have r₁ := eq66
       have r₂ := eq9230
       grind)
    | exact resolve eq66 eq9230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq9233 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq9230
       grind)
    | exact superpose eq9230 eq76
    | exact resolve eq76 eq9230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9230
  have eq9287 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9232
  have eq9305 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9233
    | exact resolve eq9233 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9233
  have eq9400 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq9287
       grind)
    | exact superpose eq9287 eq100
    | exact resolve eq100 eq9287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9287
  have eq9414 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9400
    | exact resolve eq9400 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9400
  have eq9745 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9414 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9414
  have eq9748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9745
    | exact resolve eq9745 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9745
  have eq9759 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9748
       have r₂ := eq27
       grind)
    | exact resolve eq9748 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9748
  have eq9763 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9759
    | exact resolve eq9759 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9759
  have eq9764 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9763
  have eq9767 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9764
    | exact resolve eq9764 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9764
  have eq9812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9767 eq9305
    | exact resolve eq9305 eq9767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9305 eq9767
  have eq9856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9812
  have eq9867 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9856
       have r₂ := eq27
       grind)
    | exact resolve eq9856 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9856
  have eq9870 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9867 eq27
    | exact resolve eq27 eq9867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9873 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9867 eq242
    | exact resolve eq242 eq9867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq10065 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9873 eq291
    | exact resolve eq291 eq9873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq9873
  have eq10088 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9867 eq10065
    | exact resolve eq10065 eq9867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10065
  have eq10115 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq10088
  have eq10122 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10115 eq67
    | exact resolve eq67 eq10115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq10123 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10115 eq75
    | exact resolve eq75 eq10115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq10115
  have eq10204 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq10123
    | exact resolve eq10123 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10123
  have eq10205 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10122
       have r₂ := eq9867
       grind)
    | exact resolve eq10122 eq9867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9867 eq10122
  have eq10327 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10205 eq118
    | exact resolve eq118 eq10205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq10205
  have eq10340 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq10327
  have eq10352 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10340
       have r₂ := eq9870
       grind)
    | exact resolve eq10340 eq9870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9870 eq10340
  have eq10580 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10204
       have i₂ := eq10352
       grind)
    | exact superpose eq10352 eq10204
    | exact resolve eq10204 eq10352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10204 eq10352
  have eq10624 : x = (M.op x y) := by grind
  clear eq10580
  have eq10654 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq10624 eq20
    | exact resolve eq20 eq10624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq10699 : x = (M.op (M.op x x) x) := by
    first
    | exact superpose eq10624 eq241
    | exact resolve eq241 eq10624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq10779 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq10654
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10654
    | exact resolve eq10654 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10654
  have eq10794 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq10779 eq26
    | exact resolve eq26 eq10779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq11000 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq290 (M.op x x)
       have i₂ := eq10699
       grind)
    | exact superpose eq10699 eq290
    | exact resolve eq290 eq10699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq10699
  have eq11026 : x = (M.op x x) := by
    first
    | exact superpose eq10624 eq11000
    | exact resolve eq11000 eq10624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10624 eq11000
  have eq11031 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11026
       grind)
    | exact superpose eq11026 eq76
    | exact resolve eq76 eq11026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq11032 : (k (σ y) (M.op (σ x) (σ x))) = (σ (k y x)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq11026
       grind)
    | exact superpose eq11026 eq108
    | exact resolve eq108 eq11026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq11026
  have eq11117 : (k (σ y) (σ x)) = (k (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq11032
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq11032
    | exact resolve eq11032 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq11032
  have eq11118 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10779 eq11031
    | exact resolve eq11031 eq10779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11031
  have eq11136 : (k (σ y) (σ (M.op x y))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq10779 eq11117
    | exact resolve eq11117 eq10779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11117
  have eq11137 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq11118
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11118
    | exact resolve eq11118 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11118
  have eq11145 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2726 eq11136
    | exact resolve eq11136 eq2726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2726 eq11136
  have eq11146 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10779 eq11137
    | exact resolve eq11137 eq10779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10779 eq11137
  have eq11354 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11145 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq11145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11145
  have eq11355 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq11354
  have eq11357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq10794 eq11355
    | exact resolve eq11355 eq10794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11355
  have eq11366 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq11357
       have r₂ := eq27
       grind)
    | exact resolve eq11357 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11357
  have eq11375 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10794 eq11366
    | exact resolve eq11366 eq10794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10794 eq11366
  have eq11499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11146 eq11375
    | exact resolve eq11375 eq11146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11146 eq11375
  have eq11500 : False := by grind
  exact eq11500

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
  clear eq19
  have eq84 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq78 eq54
    | exact resolve eq54 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op x x)
       have i₂ := eq54 x x x
       grind)
    | exact superpose eq54 eq12
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
  have eq122 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq807 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (M.op X0 X1)
       have i₂ := eq54 X0 X0 X1
       grind)
    | exact superpose eq54 eq100
    | (have j0 := eq100 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq100 x (M.op x x)
       have r₂ := eq54 x x x
       grind)
    | exact resolve eq100 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq84 eq100
    | (have j0 := eq100 (M.op x y) y
       grind)
    | (have r₁ := eq100 (M.op x y) y
       have r₂ := eq84 (M.op x y)
       grind)
    | exact resolve eq100 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq809 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq81 eq100
    | (have j0 := eq100 x (M.op x y)
       grind)
    | (have r₁ := eq100 x (M.op x y)
       have r₂ := eq81 x
       grind)
    | exact resolve eq100 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq815 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq809
  have eq816 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq808
  have eq817 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq807 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq831 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | exact superpose eq815 eq122
    | (have j0 := eq122 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq122 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq836 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | exact superpose eq21 eq831
    | exact resolve eq831 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq838 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq836
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq836
    | exact resolve eq836 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq839 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq838
       have i₂ := eq139 x
       grind)
    | exact superpose eq139 eq838
    | exact resolve eq838 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq840 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq839
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq839
    | exact resolve eq839 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq841 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | exact superpose eq21 eq840
    | exact resolve eq840 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq842 : (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq841
       have i₂ := eq139 x
       grind)
    | exact superpose eq139 eq841
    | exact resolve eq841 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq843 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq842
       have i₂ := eq54 (σ x) (σ x) (σ x)
       grind)
    | (have i₁ := eq842
       have i₂ := eq54 x (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) x
       grind)
    | exact superpose eq54 eq842
    | exact resolve eq842 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq844 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq843
    | exact resolve eq843 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq845 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq844
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq844
    | exact resolve eq844 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq858 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq816 eq122
    | (have j0 := eq122 y (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq122 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq863 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq21 eq858
    | exact resolve eq858 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq865 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq863
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq863
    | exact resolve eq863 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq866 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq865
       have i₂ := eq139 sF0
       grind)
    | exact superpose eq139 eq865
    | exact resolve eq865 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq867 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq21 eq866
    | exact resolve eq866 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq868 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq867
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq867
    | exact resolve eq867 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq869 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq868
       have i₂ := eq139 sF0
       grind)
    | exact superpose eq139 eq868
    | exact resolve eq868 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq870 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq869
       have i₂ := eq54 (σ sF0) (σ sF0) (σ sF0)
       grind)
    | (have i₁ := eq869
       have i₂ := eq54 x (M.op (M.op (σ sF0) (σ sF0)) (M.op (σ sF0) (σ sF0))) x
       grind)
    | exact superpose eq54 eq869
    | exact resolve eq869 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq871 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq870
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq870
    | exact resolve eq870 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq872 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq871
    | exact resolve eq871 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq2810 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq222
    | (have j0 := eq222 (M.op x y)
       grind)
    | exact resolve eq222 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq2819 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq816 eq2810
    | exact resolve eq2810 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810
  have eq2834 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq2819
    | exact resolve eq2819 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2819
  have eq10603 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq845 eq54
    | exact resolve eq54 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq11258 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq872 eq54
    | exact resolve eq54 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq12440 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11258 eq10603
    | exact resolve eq10603 eq11258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11258
  have eq12455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq12440
    | exact resolve eq12440 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12440
  have eq12457 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12455
       have r₂ := eq28
       grind)
    | exact resolve eq12455 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12455
  have eq12491 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12457 eq817
    | exact resolve eq817 eq12457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12457
  have eq12498 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12491
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq12491
    | exact resolve eq12491 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12491
  have eq12567 : (τ (σ y)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12498 eq260
    | exact resolve eq260 eq12498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq12584 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12498
  have eq12594 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38 eq12567
    | exact resolve eq12567 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12567
  have eq12609 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq40 eq12594
    | exact resolve eq12594 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12594
  have eq13252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12609 eq872
    | exact resolve eq872 eq12609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq12609
  have eq13291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13252
  have eq13311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq13291
    | exact resolve eq13291 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13291
  have eq13315 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq13311
       have r₂ := eq28
       grind)
    | exact resolve eq13311 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13311
  have eq13324 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13315 eq139
    | exact resolve eq139 eq13315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13315
  have eq13351 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq13324
    | exact resolve eq13324 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13324
  have eq13354 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13351
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13351
    | exact resolve eq13351 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13351
  have eq13402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13354 eq10603
    | exact resolve eq10603 eq13354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq13402
  have eq13441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq13428
    | exact resolve eq13428 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13428
  have eq13453 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq13441
       have r₂ := eq28
       grind)
    | exact resolve eq13441 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13441
  have eq13544 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13453 eq817
    | exact resolve eq817 eq13453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13453
  have eq13551 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13544
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq13544
    | exact resolve eq13544 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13544
  have eq13568 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13551
       have r₂ := eq12584
       grind)
    | exact resolve eq13551 eq12584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12584 eq13551
  have eq13586 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13568 eq13354
    | exact resolve eq13354 eq13568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13354
  have eq13587 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13568 eq10603
    | exact resolve eq10603 eq13568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13568
  have eq13613 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13587
  have eq13614 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13586
  have eq13640 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13614 eq27
    | exact resolve eq27 eq13614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13644 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13614 eq40
    | exact resolve eq40 eq13614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13614
  have eq13700 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq39 eq13644
    | exact resolve eq13644 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13644
  have eq13709 : y = (τ (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13700 eq40
    | exact resolve eq40 eq13700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13700
  have eq13756 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq13709
    | exact resolve eq13709 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13709
  have eq13764 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq13756 eq39
    | exact resolve eq39 eq13756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13756
  have eq13812 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq13764
    | exact resolve eq13764 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13764
  have eq15474 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13640 eq13613
    | exact resolve eq13613 eq13640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13613 eq13640
  have eq15503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15474
  have eq15520 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq15503
       have r₂ := eq28
       grind)
    | exact resolve eq15503 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15503
  have eq15531 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15520 eq40
    | exact resolve eq40 eq15520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15520
  have eq15578 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq15531
    | exact resolve eq15531 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15531
  have eq15586 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15578 eq39
    | exact resolve eq39 eq15578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15578
  have eq15634 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq15586
    | exact resolve eq15586 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15586
  have eq15638 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15634 eq21
    | exact resolve eq21 eq15634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15639 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15634 eq78
    | exact resolve eq78 eq15634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq15665 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq15634
  have eq15666 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15638
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15638
    | exact resolve eq15638 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15638
  have eq16140 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15639 (M.op y x)
       have i₂ := eq15639 x
       grind)
    | exact superpose eq15639 eq15639
    | exact resolve eq15639 eq15639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15639
  have eq16154 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq16140
  have eq16175 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139 y
       have i₂ := eq16154
       grind)
    | exact superpose eq16154 eq139
    | exact resolve eq139 eq16154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16154
  have eq16203 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16175
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16175
    | exact resolve eq16175 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16175
  have eq16206 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15666 eq16203
    | exact resolve eq16203 eq15666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15666 eq16203
  have eq16257 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq16206
  have eq16312 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16257 eq2834
    | exact resolve eq2834 eq16257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2834
  have eq16375 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43 eq16312
    | exact resolve eq16312 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq16312
  have eq16861 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq13812 eq16375
    | exact resolve eq16375 eq13812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13812 eq16375
  have eq16909 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq16861
  have eq16942 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16909
       have r₂ := eq15665
       grind)
    | exact resolve eq16909 eq15665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15665 eq16909
  have eq16945 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16942
       have i₂ := eq101 y
       grind)
    | exact superpose eq101 eq16942
    | exact resolve eq16942 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16942
  have eq16947 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16945
       have i₂ := eq139 y
       grind)
    | exact superpose eq139 eq16945
    | exact resolve eq16945 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16945
  have eq16949 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16947
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16947
    | exact resolve eq16947 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16947
  have eq16990 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16949 eq817
    | exact resolve eq817 eq16949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16949
  have eq17001 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16990
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq16990
    | exact resolve eq16990 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16990
  have eq17055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17001 eq10603
    | exact resolve eq10603 eq17001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10603 eq17001
  have eq17095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17055
    | exact resolve eq17055 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17055
  have eq17107 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17095
       have r₂ := eq28
       grind)
    | exact resolve eq17095 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17095
  have eq35312 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17107 eq817
    | exact resolve eq817 eq17107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq17107
  have eq35321 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35312
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq35312
    | exact resolve eq35312 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq35312
  have eq37059 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35321 eq16257
    | exact resolve eq16257 eq35321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16257 eq35321
  have eq37125 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq37059
  have eq37157 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37125 eq39
    | exact resolve eq39 eq37125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq37125
  have eq37211 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq37157
    | exact resolve eq37157 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq37157
  have eq37212 : x = (M.op x y) := by grind
  clear eq37211
  have eq37217 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37212 eq21
    | exact resolve eq21 eq37212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq37226 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq37212 eq81
    | exact resolve eq81 eq37212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq37293 : x = (k y (M.op x x)) := by
    first
    | exact superpose eq37212 eq816
    | exact resolve eq816 eq37212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq37212
  have eq40688 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37217
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37217
    | exact resolve eq37217 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37217
  have eq41030 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq40688 eq23
    | exact resolve eq23 eq40688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq41031 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq40688 eq27
    | exact resolve eq27 eq40688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41043 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40688 eq135
    | exact resolve eq135 eq40688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq43013 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | exact superpose eq40688 eq41043
    | exact resolve eq41043 eq40688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40688 eq41043
  have eq43561 : x = (M.op x x) := by
    first
    | (have i₁ := eq37226 (M.op x x)
       have i₂ := eq37226 x
       grind)
    | exact superpose eq37226 eq37226
    | exact resolve eq37226 eq37226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37226
  have eq43625 : x = (k y x) := by
    first
    | (have i₁ := eq37293
       have i₂ := eq43561
       grind)
    | exact superpose eq43561 eq37293
    | exact resolve eq37293 eq43561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37293
  have eq43783 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43013
       have i₂ := eq43625
       grind)
    | exact superpose eq43625 eq43013
    | exact resolve eq43013 eq43625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43013 eq43625
  have eq43810 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43783
       have i₂ := eq41030
       grind)
    | exact superpose eq41030 eq43783
    | exact resolve eq43783 eq41030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43783
  have eq43811 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq43810
  have eq43873 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq139 x
       have i₂ := eq43561
       grind)
    | exact superpose eq43561 eq139
    | exact resolve eq139 eq43561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq43561
  have eq43928 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43873
       have i₂ := eq41030
       grind)
    | exact superpose eq41030 eq43873
    | exact resolve eq43873 eq41030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41030 eq43873
  have eq44105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq43928 eq43811
    | exact resolve eq43811 eq43928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43811
  have eq44122 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq44105
       have r₂ := eq28
       grind)
    | exact resolve eq44105 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44105
  have eq45188 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq44122 eq41031
    | exact resolve eq41031 eq44122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41031 eq44122
  have eq45230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43928 eq45188
    | exact resolve eq45188 eq43928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43928 eq45188
  have eq45709 : False := by grind
  exact eq45709

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq24 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X0) (σ X1)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq86
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq86
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq109 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq23 X2 X0 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (σ X0) (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) (σ X0) X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq685 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq195
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq195
    | (have j1 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq195 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq195
  have eq686 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq685
  have eq3843 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x y) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq24 y x x
       have i₂ := eq686
       grind)
    | exact superpose eq686 eq24
    | exact resolve eq24 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3851 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq109 x x y
       have i₂ := eq686
       grind)
    | exact superpose eq686 eq109
    | exact resolve eq109 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq43232 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3843 (M.op y x)
       have i₂ := eq23 x y x
       grind)
    | exact superpose eq23 eq3843
    | exact resolve eq3843 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843
  have eq43677 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq175 y (σ x)
       have i₂ := eq43232
       grind)
    | exact superpose eq43232 eq175
    | exact resolve eq175 eq43232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44119 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq109 (σ y) (σ (M.op y y)) (σ x)
       have i₂ := eq43677
       grind)
    | exact superpose eq43677 eq109
    | exact resolve eq109 eq43677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq43677
  have eq44169 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44119
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq44119
    | exact resolve eq44119 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44119
  have eq44571 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (σ x) (σ y)
       have i₂ := eq44169
       grind)
    | exact superpose eq44169 eq23
    | exact resolve eq23 eq44169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44169
  have eq45426 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44571 (σ y)
       have i₂ := eq43232
       grind)
    | exact superpose eq43232 eq44571
    | exact resolve eq44571 eq43232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43232 eq44571
  have eq45499 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq45426
  have eq45515 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45499
       have i₂ := eq174 y (σ x)
       grind)
    | exact superpose eq174 eq45499
    | exact resolve eq45499 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45499
  have eq45772 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq174 y X0
       have i₂ := eq45515
       grind)
    | exact superpose eq45515 eq174
    | exact resolve eq174 eq45515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47603 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45772 (σ y)
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq45772
    | exact resolve eq45772 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45772
  have eq50015 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47603
       have i₂ := eq45515
       grind)
    | exact superpose eq45515 eq47603
    | exact resolve eq47603 eq45515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45515 eq47603
  have eq50079 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq50015
  have eq50100 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50079
       have i₂ := eq98 (M.op x y)
       grind)
    | exact superpose eq98 eq50079
    | exact resolve eq50079 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50079
  have eq50116 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq50100
       grind)
    | exact superpose eq50100 eq10
    | exact resolve eq10 eq50100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50100
  have eq50378 : x = y ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50116
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq50116
    | exact resolve eq50116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50116
  have eq50700 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50378
       grind)
    | exact superpose eq50378 eq16
    | exact resolve eq16 eq50378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50378
  have eq50701 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq50700
       have r₂ := eq98 x
       grind)
    | exact resolve eq50700 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50700
  have eq106860 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3851 (M.op x x)
       have i₂ := eq23 x x y
       grind)
    | exact superpose eq23 eq3851
    | exact resolve eq3851 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851
  have eq106999 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq174 x (σ y)
       have i₂ := eq106860
       grind)
    | exact superpose eq106860 eq174
    | exact resolve eq174 eq106860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq107828 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24 (σ x) (σ y) (σ (M.op x x))
       have i₂ := eq106999
       grind)
    | exact superpose eq106999 eq24
    | exact resolve eq24 eq106999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq106999
  have eq107965 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107828
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq107828
    | exact resolve eq107828 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107828
  have eq108738 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) (σ y) X0
       have i₂ := eq107965
       grind)
    | exact superpose eq107965 eq23
    | exact resolve eq23 eq107965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107965
  have eq110306 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq108738 (σ x)
       have i₂ := eq106860
       grind)
    | exact superpose eq106860 eq108738
    | exact resolve eq108738 eq106860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106860 eq108738
  have eq110443 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq110306
  have eq110471 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq110443
       have i₂ := eq175 x (σ y)
       grind)
    | exact superpose eq175 eq110443
    | exact resolve eq110443 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq110443
  have eq111157 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50701
       have i₂ := eq110471
       grind)
    | exact superpose eq110471 eq50701
    | exact resolve eq50701 eq110471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50701 eq110471
  have eq111312 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq111157
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq111157
       have i₂ := eq23 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq23 eq111157
    | exact resolve eq111157 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq111157
  have eq111313 : (σ x) = (σ y) := by grind
  clear eq111312
  have eq111338 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq111313
       grind)
    | exact superpose eq111313 eq10
    | exact resolve eq10 eq111313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111313
  have eq111802 : x = y := by
    first
    | (have i₁ := eq111338
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq111338
    | exact resolve eq111338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111338
  have eq111805 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111802
       grind)
    | exact superpose eq111802 eq16
    | exact resolve eq16 eq111802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111802
  have eq111857 : False := by grind
  exact eq111857
