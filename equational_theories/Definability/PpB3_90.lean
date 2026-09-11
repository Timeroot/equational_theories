import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op x X0) (M.op x x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  have eq49 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 ∨ (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) := by
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq49 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq105 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (k X1 (σ X2))
       have i₂ := eq26 X1 X2 X0
       grind)
    | exact superpose eq26 eq14
    | (have j0 := eq14 (k X1 (σ X2)) (σ X0)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op (M.op X0 X1) (M.op X0 X2)) ∨ (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op X1 (M.op (M.op X0 X1) (M.op X0 X2))) ∨ (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X1) (M.op X0 X2))
       have i₂ := eq52 X1 X0 X2
       grind)
    | exact superpose eq52 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X1) (M.op X0 X2))
       have j1 := eq52 X1 X0 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq52 X0 X1 X2
       grind)
    | exact resolve eq12 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq291 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op X1 (M.op (M.op X0 X1) (M.op X0 X2))) ∨ (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq280 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq292 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = X1 ∨ (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq291 X0 X1 X2
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq291
    | (have j0 := eq291 X0 X1 X2
       grind)
    | exact resolve eq291 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq293 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq292 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq301 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1 (M.op (M.op x X0) x)
       have i₂ := eq20 x X0
       grind)
    | exact superpose eq20 eq293
    | exact resolve eq293 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq293
  have eq330 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (τ X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (τ X0)) X1)
       have i₂ := eq301 X1 (τ X0)
       grind)
    | exact superpose eq301 eq17
    | exact resolve eq17 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq333 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 (τ X0)) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq330
    | exact resolve eq330 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq388 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op X1 (τ (τ X0))) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op X1 (τ (τ X0))) X1))
       have i₂ := eq333 (τ X0) X1
       grind)
    | exact superpose eq333 eq17
    | exact resolve eq17 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq395 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op X1 (τ (τ X0))) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq388
    | exact resolve eq388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq633 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (M.op X1 (τ (τ (τ X0)))) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op (M.op X1 (τ (τ (τ X0)))) X1)))
       have i₂ := eq395 (τ X0) X1
       grind)
    | exact superpose eq395 eq17
    | exact resolve eq17 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq640 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op (M.op X1 (τ (τ (τ X0)))) X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq633
    | exact resolve eq633 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq1504 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ X0))))) X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ X0))))) X1))))
       have i₂ := eq640 (τ X0) X1
       grind)
    | exact superpose eq640 eq17
    | exact resolve eq17 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq1517 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ X0))))) X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1504 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1504
    | exact resolve eq1504 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1960 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ (τ X0)))))) X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ (τ X0)))))) X1)))))
       have i₂ := eq1517 (τ X0) X1
       grind)
    | exact superpose eq1517 eq17
    | exact resolve eq17 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1973 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ (τ X0)))))) X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1960 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1960
    | exact resolve eq1960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq4052 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ (τ (τ X0))))))) X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ (τ (τ X0))))))) X1))))))
       have i₂ := eq1973 (τ X0) X1
       grind)
    | exact superpose eq1973 eq17
    | exact resolve eq17 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq4066 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ (τ (τ X0))))))) X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4052 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4052
    | exact resolve eq4052 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4052
  have eq15916 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (τ X0)))))))) X1))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (τ X0)))))))) X1)))))))
       have i₂ := eq4066 (τ X0) X1
       grind)
    | exact superpose eq4066 eq17
    | exact resolve eq17 eq4066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq15969 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (τ X0)))))))) X1))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15916 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15916
    | exact resolve eq15916 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15916
  have eq99362 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X2) (k X0 (σ X1))
       have i₂ := eq105 X2 X0 X1
       grind)
    | exact superpose eq105 eq12
    | (have j0 := eq12 (σ X2) (k X0 (σ X1))
       have j1 := eq105 X2 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (k X1 (σ X2))
       have r₂ := eq105 X0 X1 X2
       grind)
    | (have r₁ := eq12 (k X1 (σ X2)) (σ X0)
       have r₂ := eq105 X0 X1 X2
       grind)
    | exact resolve eq12 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq99527 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq99362 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99362
  have eq99564 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99527 X0 X1 X2
       have i₂ := eq26 X0 X1 X2
       grind)
    | exact superpose eq26 eq99527
    | (have j0 := eq99527 X0 X1 X2
       grind)
    | exact resolve eq99527 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq99527
  have eq99565 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq99564 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99564
  have eq326026 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (k X1 (k (τ X0) (σ (σ (σ (σ (σ (σ (M.op (M.op X2 (τ (τ (τ (τ (τ (τ (τ X0)))))))) X2)))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99565 X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (τ X0)))))))) X1))))))) X2
       have i₂ := eq15969 X0 X1
       grind)
    | exact superpose eq15969 eq99565
    | exact resolve eq99565 eq15969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15969 eq99565
  have eq326526 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq326026 X0 X1 x
       have i₂ := eq4066 (τ X0) x
       grind)
    | exact superpose eq4066 eq326026
    | (have j0 := eq326026 X0 X1 x
       grind)
    | exact resolve eq326026 eq4066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4066 eq326026
  have eq326710 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq326526 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq326526
    | (have j0 := eq326526 X0 X1
       grind)
    | exact resolve eq326526 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326526
  have eq326787 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq326710 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq326710
    | exact resolve eq326710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq326710 (σ X1) X0
       grind)
    | exact superpose eq326710 eq15
    | (have j1 := eq326710 (σ X1) X0
       grind)
    | exact resolve eq15 eq326710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326710
  have eq330634 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq326787 X0 (τ X1)
       grind)
    | exact superpose eq326787 eq18
    | (have j1 := eq326787 X0 (τ X1)
       grind)
    | exact resolve eq18 eq326787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq326787
  have eq396129 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq330634 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq330634
    | exact resolve eq330634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330634
  have eq397093 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq396129 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq396129
    | (have j0 := eq396129 X0 X1
       grind)
    | exact resolve eq396129 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396129
  have eq452500 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq327103 x y
       grind)
    | exact superpose eq327103 eq16
    | (have j1 := eq327103 x y
       grind)
    | exact resolve eq16 eq327103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453352 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq327103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327103
  have eq462239 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq452500
       have i₂ := eq397093 y x
       grind)
    | exact superpose eq397093 eq452500
    | (have j1 := eq397093 (σ y) (σ x)
       grind)
    | (have r₁ := eq452500
       have r₂ := eq397093 y x
       grind)
    | exact resolve eq452500 eq397093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462245 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq462239
  have eq462254 : x ≠ x ∨ x = (k x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq462245
       grind)
    | exact superpose eq462245 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq462245
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq462245
       grind)
    | exact resolve eq13 eq462245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462245
  have eq462522 : x = (k x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq462254
  have eq628920 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq453352 x y
       have i₂ := eq462522
       grind)
    | exact superpose eq462522 eq453352
    | (have j0 := eq453352 x y
       grind)
    | exact resolve eq453352 eq462522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453352 eq462522
  have eq628933 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq628920
  have eq628934 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq628933
  have eq630788 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq628934
       grind)
    | exact superpose eq628934 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq628934
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq628934
       grind)
    | exact resolve eq12 eq628934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628934
  have eq631106 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq630788
  have eq632808 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq452500
       have i₂ := eq631106
       grind)
    | exact superpose eq631106 eq452500
    | exact resolve eq452500 eq631106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452500 eq631106
  have eq632927 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq632808
  have eq632928 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq632927
  have eq634346 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq632928
       grind)
    | exact superpose eq632928 eq16
    | exact resolve eq16 eq632928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634488 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq632928
       grind)
    | exact superpose eq632928 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq632928
       grind)
    | exact resolve eq13 eq632928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634804 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq634488
  have eq634900 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq634804
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq634804
    | exact resolve eq634804 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634804
  have eq690120 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq634900
       grind)
    | exact superpose eq634900 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq634900
       grind)
    | exact resolve eq12 eq634900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634900
  have eq690450 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq690120
  have eq690553 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq690450
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq690450
    | exact resolve eq690450 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690450
  have eq690664 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq690553
       have i₂ := eq632928
       grind)
    | exact superpose eq632928 eq690553
    | exact resolve eq690553 eq632928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632928 eq690553
  have eq690665 : (σ x) = (σ (k x y)) := by grind
  clear eq690664
  have eq693957 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq397093 y x
       have i₂ := eq690665
       grind)
    | exact superpose eq690665 eq397093
    | (have j0 := eq397093 y x
       grind)
    | exact resolve eq397093 eq690665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397093 eq690665
  have eq694809 : x = (M.op x y) := by
    first
    | (have r₁ := eq693957
       have r₂ := eq634346
       grind)
    | exact resolve eq693957 eq634346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693957
  have eq696053 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq634346
       have i₂ := eq694809
       grind)
    | exact superpose eq694809 eq634346
    | exact resolve eq634346 eq694809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634346 eq694809
  have eq696389 : False := by grind
  exact eq696389

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq296 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq296 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq296
    | (have j0 := eq296 (σ X0) (σ X1)
       grind)
    | exact resolve eq296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq296 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq296
    | (have j0 := eq296 (τ X0) (τ X1)
       grind)
    | exact resolve eq296 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq454 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq297 X0 X1
       have i₂ := eq296 X0 X1
       grind)
    | exact superpose eq296 eq297
    | (have j0 := eq297 X0 X1
       have j1 := eq296 (σ X0) (σ X1)
       grind)
    | exact resolve eq297 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq611 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq601 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq601
    | (have j0 := eq601 (σ X0) (σ X1)
       grind)
    | exact resolve eq601 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq621 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq611 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq611
    | (have j0 := eq611 X0 X1
       grind)
    | exact resolve eq611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq623 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq621 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq621
    | (have j0 := eq621 X0 X1
       grind)
    | exact resolve eq621 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq624 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq623 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq623
    | (have j0 := eq623 X0 X1
       grind)
    | exact resolve eq623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq625 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq624
    | (have j0 := eq624 X0 X1
       grind)
    | exact resolve eq624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq628 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq625 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq625
    | (have j0 := eq625 (σ X0) (σ X1)
       grind)
    | exact resolve eq625 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq6420 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq454 x y
       grind)
    | exact superpose eq454 eq16
    | (have j1 := eq454 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq454 x y
       grind)
    | exact resolve eq16 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq6467 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6420
  have eq6486 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6467
       grind)
    | exact superpose eq6467 eq16
    | exact resolve eq16 eq6467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6492 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq6467
       grind)
    | exact superpose eq6467 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq6467
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6467
       grind)
    | exact resolve eq13 eq6467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6515 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6492
  have eq6519 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6515
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq6515
    | exact resolve eq6515 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6515
  have eq6522 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq296 eq6519
    | (have j1 := eq296 x y
       grind)
    | exact resolve eq6519 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6519
  have eq6523 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6522
       have r₂ := eq6486
       grind)
    | exact resolve eq6522 eq6486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6522
  have eq6533 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq6523
       grind)
    | exact superpose eq6523 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6523
       grind)
    | exact resolve eq12 eq6523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6523
  have eq6559 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6533
  have eq6562 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6559
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq6559
    | exact resolve eq6559 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6559
  have eq6568 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6467 eq6562
    | exact resolve eq6562 eq6467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6467 eq6562
  have eq6571 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq296 eq6568
    | (have j1 := eq296 x y
       grind)
    | exact resolve eq6568 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq6568
  have eq6573 : y = (M.op x y) := by
    first
    | (have r₁ := eq6571
       have r₂ := eq6486
       grind)
    | exact resolve eq6571 eq6486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6486 eq6571
  have eq6574 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6573
       grind)
    | exact superpose eq6573 eq16
    | exact resolve eq16 eq6573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6578 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq6573
       grind)
    | exact superpose eq6573 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6573
       grind)
    | exact resolve eq13 eq6573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6601 : y = (k x y) ∨ y = (M.op y x) := by grind
  clear eq6578
  have eq7044 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq297 x y
       have i₂ := eq6601
       grind)
    | exact superpose eq6601 eq297
    | (have j0 := eq297 x y
       grind)
    | exact resolve eq297 eq6601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq6601
  have eq7057 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq7044
  have eq7063 : y = (M.op y x) := by
    first
    | (have r₁ := eq7057
       have r₂ := eq6574
       grind)
    | exact resolve eq7057 eq6574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7057
  have eq7070 : y ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq7063
       grind)
    | exact superpose eq7063 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7063
       grind)
    | exact resolve eq12 eq7063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7063
  have eq7096 : (M.op x y) = (k x y) := by grind
  clear eq7070
  have eq7098 : y = (k x y) := by
    first
    | (have i₁ := eq7096
       have i₂ := eq6573
       grind)
    | exact superpose eq6573 eq7096
    | exact resolve eq7096 eq6573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6573 eq7096
  have eq7183 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq628 x y
       have i₂ := eq7098
       grind)
    | exact superpose eq7098 eq628
    | (have j0 := eq628 x y
       grind)
    | exact resolve eq628 eq7098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq7098
  have eq7186 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7183
  have eq7193 : False := by grind
  exact eq7193

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq45 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq48
    | exact resolve eq48 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq48
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq55 X1
       grind)
    | exact superpose eq55 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq94 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq192 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq196 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq192 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq206 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq94 X1 (σ X0)
       grind)
    | (have r₁ := eq196 X0 X0
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq196 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq196
  have eq213 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq206 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq206
    | (have j0 := eq206 X0 X1
       grind)
    | exact resolve eq206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq214 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq220 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq214 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq214
    | exact resolve eq214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214 x y
       grind)
    | exact superpose eq214 eq16
    | exact resolve eq16 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq293 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq220 X0 (τ X1)
       grind)
    | exact superpose eq220 eq18
    | exact resolve eq18 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq220
  have eq306 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq293
    | exact resolve eq293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq312 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq306
    | exact resolve eq306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq324 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq231
       have i₂ := eq312 x y
       grind)
    | exact superpose eq312 eq231
    | exact resolve eq231 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq312
  have eq325 : False := by grind
  exact eq325

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq288 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq288 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq291 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq289 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq289 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq289 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq302 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq291 (σ X0)
       grind)
    | exact superpose eq291 eq15
    | exact resolve eq15 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq291 (τ X0)
       grind)
    | exact superpose eq291 eq31
    | exact resolve eq31 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq308 X0
       have i₂ := eq291 X0
       grind)
    | exact superpose eq291 eq308
    | exact resolve eq308 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq321 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq302 X0
       have i₂ := eq291 X0
       grind)
    | exact superpose eq291 eq302
    | exact resolve eq302 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq302
  have eq369 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq321 X0
       grind)
    | exact superpose eq321 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq321 X0
       grind)
    | exact superpose eq321 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq369 X0 X1
       have j1 := eq371 X0 X1
       grind)
    | (have r₁ := eq369 X0 X1
       have r₂ := eq371 X0 X1
       grind)
    | exact resolve eq369 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq371
  have eq583 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq372 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq372
    | exact resolve eq372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq372 X1 (σ X0)
       grind)
    | exact superpose eq372 eq15
    | (have j1 := eq372 X1 (σ X0)
       grind)
    | exact resolve eq15 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq653 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq583 (τ X1) X0
       grind)
    | exact superpose eq583 eq18
    | (have j1 := eq583 (τ X1) X0
       grind)
    | exact resolve eq18 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq583
  have eq898 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq653
    | exact resolve eq653 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq951 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq898 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq898
    | (have j0 := eq898 X0 X1
       grind)
    | exact resolve eq898 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq962 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq951 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq951
    | (have j0 := eq951 (τ X1) (τ X0)
       grind)
    | exact resolve eq951 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1012 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq962 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq962
    | (have j0 := eq962 X0 X1
       grind)
    | exact resolve eq962 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1537 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq594 x y
       grind)
    | exact superpose eq594 eq16
    | (have j1 := eq594 x y
       grind)
    | exact resolve eq16 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1574 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq594 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq1637 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1574 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1574
    | (have j0 := eq1574 (τ X0) (τ X1)
       grind)
    | exact resolve eq1574 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1645 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1637 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1637
    | (have j0 := eq1637 X0 X1
       grind)
    | exact resolve eq1637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq1648 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1645 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1645
    | (have j0 := eq1645 X0 X1
       grind)
    | exact resolve eq1645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1649 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1648 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1648
    | (have j0 := eq1648 X0 X1
       grind)
    | exact resolve eq1648 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1650 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1649 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1649
    | (have j0 := eq1649 X0 X1
       grind)
    | exact resolve eq1649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq2777 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq1012 X0 X1
       grind)
    | exact superpose eq1012 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq1012 X1 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq1012 X0 X1
       grind)
    | exact resolve eq13 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq2785 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2777 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq2792 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X1 X1)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2785 X0 X1
       have i₂ := eq315 X1
       grind)
    | exact superpose eq315 eq2785
    | (have j0 := eq2785 X0 X1
       grind)
    | exact resolve eq2785 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq2785
  have eq2814 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2792 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2792
    | (have j0 := eq2792 X0 X1
       grind)
    | exact resolve eq2792 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2792
  have eq361092 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ X1) = (τ (k X1 X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq2814 X1 X0
       grind)
    | exact superpose eq2814 eq11
    | (have j1 := eq2814 X1 X0
       grind)
    | exact resolve eq11 eq2814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2814
  have eq361490 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (τ (k X1 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq361092 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq361092
    | (have j0 := eq361092 X0 X1
       grind)
    | exact resolve eq361092 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361092
  have eq361708 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (k (σ X0) X1)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq361490 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq361490
    | (have j0 := eq361490 X1 X1
       grind)
    | exact resolve eq361490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361490
  have eq362413 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq361708 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq361708
    | (have j0 := eq361708 X0 X1
       grind)
    | exact resolve eq361708 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361708
  have eq362895 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (k X0 (τ X1)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 (τ X1))
       have i₂ := eq362413 X0 X1
       grind)
    | exact superpose eq362413 eq10
    | (have j1 := eq362413 X0 X1
       grind)
    | exact resolve eq10 eq362413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362413
  have eq363161 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (k X0 (τ X1)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq362895 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq362895
    | (have j0 := eq362895 X0 X1
       grind)
    | exact resolve eq362895 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq362895
  have eq363575 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq363161 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq363161
    | (have j0 := eq363161 X0 (σ X0)
       grind)
    | exact resolve eq363161 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363161
  have eq364130 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq363575 X0 X1
       have i₂ := eq321 X0
       grind)
    | exact superpose eq321 eq363575
    | (have j0 := eq363575 X0 X1
       grind)
    | exact resolve eq363575 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq363575
  have eq365796 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq364130 X0 X1
       grind)
    | exact superpose eq364130 eq10
    | (have j1 := eq364130 X0 X1
       grind)
    | exact resolve eq10 eq364130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364130
  have eq366109 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365796 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq365796
    | (have j0 := eq365796 X0 X1
       grind)
    | exact resolve eq365796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365796
  have eq366202 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq366109 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq366109 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq366109 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366109
  have eq366927 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1537
       have i₂ := eq366202 y x
       grind)
    | exact superpose eq366202 eq1537
    | (have j1 := eq366202 y x
       grind)
    | exact resolve eq1537 eq366202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq366929 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq366202 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366202
  have eq366930 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq366927
  have eq381238 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq366929 (σ x) (σ y)
       have i₂ := eq366930
       grind)
    | exact superpose eq366930 eq366929
    | (have j0 := eq366929 (σ x) (σ y)
       grind)
    | (have r₁ := eq366929 (σ x) (σ y)
       have r₂ := eq366930
       grind)
    | exact resolve eq366929 eq366930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366930
  have eq381244 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq381238
  have eq381252 : x = (k x y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq381244
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq381244
    | exact resolve eq381244 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381244
  have eq381424 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq1574 x y
       have i₂ := eq381252
       grind)
    | exact superpose eq381252 eq1574
    | (have j0 := eq1574 x y
       grind)
    | (have r₁ := eq1574 x y
       have r₂ := eq381252
       grind)
    | exact resolve eq1574 eq381252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381252
  have eq381608 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq381424
  have eq381613 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1574 x y
       grind)
    | (have r₁ := eq381608
       have r₂ := eq1574 x y
       grind)
    | exact resolve eq381608 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574 eq381608
  have eq381621 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq381613
       grind)
    | exact superpose eq381613 eq16
    | exact resolve eq16 eq381613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381754 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq366929 (σ x) (σ y)
       have i₂ := eq381613
       grind)
    | exact superpose eq381613 eq366929
    | (have j0 := eq366929 (σ x) (σ y)
       grind)
    | (have r₁ := eq366929 (σ x) (σ y)
       have r₂ := eq381613
       grind)
    | exact resolve eq366929 eq381613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366929 eq381613
  have eq381760 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq381754
  have eq381768 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq381760
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq381760
    | exact resolve eq381760 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381760
  have eq381946 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq381768
       grind)
    | exact superpose eq381768 eq10
    | exact resolve eq10 eq381768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381768
  have eq382244 : x = (k x y) := by
    first
    | (have i₁ := eq381946
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq381946
    | exact resolve eq381946 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381946
  have eq382304 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1650 x y
       have i₂ := eq382244
       grind)
    | exact superpose eq382244 eq1650
    | (have j0 := eq1650 x y
       grind)
    | (have r₁ := eq1650 x y
       have r₂ := eq382244
       grind)
    | exact resolve eq1650 eq382244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650 eq382244
  have eq382484 : x = (M.op x y) := by grind
  clear eq382304
  have eq382499 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq381621
       have i₂ := eq382484
       grind)
    | exact superpose eq382484 eq381621
    | exact resolve eq381621 eq382484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381621 eq382484
  have eq382601 : False := by grind
  exact eq382601

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq283 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq285 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq287 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq283 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq288 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq286 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq286 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq286 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq299 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq288 (σ X0)
       grind)
    | exact superpose eq288 eq15
    | exact resolve eq15 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq299 X0
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq299
    | exact resolve eq299 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq299
  have eq368 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq287 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq639 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq638 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq654 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq639 (σ X0) (σ X1)
       grind)
    | exact superpose eq639 eq15
    | (have j1 := eq639 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq639 (τ X0) X1
       grind)
    | exact superpose eq639 eq17
    | (have j1 := eq639 (τ X0) X1
       grind)
    | exact resolve eq17 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq639
  have eq866 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq662 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq662
    | exact resolve eq662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq937 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq866 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq866
    | (have j0 := eq866 X0 X1
       grind)
    | exact resolve eq866 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq1580 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq654 x y
       grind)
    | exact superpose eq654 eq16
    | (have j1 := eq654 x y
       grind)
    | exact resolve eq16 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1617 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq654 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq1793 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1580
       have i₂ := eq937 x y
       grind)
    | exact superpose eq937 eq1580
    | (have j1 := eq937 (σ x) (σ y)
       grind)
    | (have r₁ := eq1580
       have r₂ := eq937 x y
       grind)
    | exact resolve eq1580 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1580
  have eq1794 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1793
  have eq1799 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1794
       grind)
    | exact superpose eq1794 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1794
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1794
       grind)
    | exact resolve eq13 eq1794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq1804 : y = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1799
  have eq2956 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1617 x y
       have i₂ := eq1804
       grind)
    | exact superpose eq1804 eq1617
    | (have j0 := eq1617 x y
       grind)
    | exact resolve eq1617 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617 eq1804
  have eq2963 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2956
  have eq2964 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2963
  have eq2970 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2964
       grind)
    | exact superpose eq2964 eq16
    | exact resolve eq16 eq2964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2976 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2964
       grind)
    | exact superpose eq2964 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2964
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq2964
       grind)
    | exact resolve eq13 eq2964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2964
  have eq2984 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2976
  have eq2986 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2984
       have i₂ := eq318 y
       grind)
    | exact superpose eq318 eq2984
    | exact resolve eq2984 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq2984
  have eq2988 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2986
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2986
    | exact resolve eq2986 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq5571 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq937 x y
       have i₂ := eq2988
       grind)
    | exact superpose eq2988 eq937
    | (have j0 := eq937 x y
       grind)
    | exact resolve eq937 eq2988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937 eq2988
  have eq5633 : y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq5571
       have r₂ := eq2970
       grind)
    | exact resolve eq5571 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5571
  have eq5666 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2970
       have i₂ := eq5633
       grind)
    | exact superpose eq5633 eq2970
    | exact resolve eq2970 eq5633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2970 eq5633
  have eq5689 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq5666
  have eq5690 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq5689
  have eq5707 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5690
       grind)
    | exact superpose eq5690 eq10
    | exact resolve eq10 eq5690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5690
  have eq5770 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5707
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5707
    | exact resolve eq5707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5707
  have eq5771 : y = (M.op y y) := by grind
  clear eq5770
  have eq5780 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq5771
       grind)
    | exact superpose eq5771 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq5771
       grind)
    | exact resolve eq12 eq5771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5789 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq368 y X0
       have i₂ := eq5771
       grind)
    | exact superpose eq5771 eq368
    | (have j0 := eq368 y X0
       grind)
    | exact resolve eq368 eq5771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq5771
  have eq5834 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq5789 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5789
  have eq5835 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq5780 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5780
  have eq6194 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq5834 (σ X0)
       grind)
    | exact superpose eq5834 eq15
    | exact resolve eq15 eq5834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5834
  have eq6227 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq6194 X0
       have i₂ := eq5835 X0
       grind)
    | exact superpose eq5835 eq6194
    | exact resolve eq6194 eq5835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5835 eq6194
  have eq6672 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6227 x
       grind)
    | exact superpose eq6227 eq16
    | (have r₁ := eq16
       have r₂ := eq6227 x
       grind)
    | exact resolve eq16 eq6227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6227
  have eq6743 : False := by grind
  exact eq6743

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation837 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq467 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq692 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq5463 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq692 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq692
    | (have j0 := eq692 (σ X0) (σ X1)
       grind)
    | exact resolve eq692 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq5584 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5463 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq5463
    | (have j0 := eq5463 X0 X1
       grind)
    | exact resolve eq5463 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463
  have eq30257 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq467 (σ X0) (σ (σ X1))
       have i₂ := eq5584 X0 X1
       grind)
    | exact superpose eq5584 eq467
    | (have j0 := eq467 (σ X0) (σ (σ X1))
       have j1 := eq5584 X0 X1
       grind)
    | exact resolve eq467 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq30328 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5584 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5584
  have eq30332 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq30257 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30257
  have eq30370 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30332 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq30332
    | (have j0 := eq30332 X0 X1
       grind)
    | exact resolve eq30332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30332
  have eq30371 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq30370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30370
  have eq30506 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (k (σ X0) (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30371 X0 X1
       have i₂ := eq15 (σ X0) (σ X1)
       grind)
    | exact superpose eq15 eq30371
    | (have j0 := eq30371 X0 X1
       grind)
    | exact resolve eq30371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30371
  have eq30568 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30506 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq30506
    | (have j0 := eq30506 X0 X1
       grind)
    | exact resolve eq30506 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30506
  have eq30608 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30568 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq30568
    | (have j0 := eq30568 X0 X1
       grind)
    | exact resolve eq30568 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30568
  have eq30628 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30608 X0 X1
       have j1 := eq30328 X0 X1
       grind)
    | (have r₁ := eq30608 X0 X1
       have r₂ := eq30328 X0 X1
       grind)
    | (have r₁ := eq30608 (M.op X0 X0) (k X0 X1)
       have r₂ := eq30328 X0 X1
       grind)
    | (have r₁ := eq30608 (k X0 X1) (M.op X0 X0)
       have r₂ := eq30328 X0 X1
       grind)
    | exact resolve eq30608 eq30328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30328 eq30608
  have eq30696 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ X0)) = (σ (σ (k X1 (τ X0)))) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30628 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30628
    | exact resolve eq30628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30628
  have eq30885 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ X0)) = (σ (k (σ X1) X0)) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30696 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq30696
    | (have j0 := eq30696 X0 X1
       grind)
    | exact resolve eq30696 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq30696
  have eq30952 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30885 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30885
    | exact resolve eq30885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30885
  have eq31189 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30952 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq30952
    | (have j0 := eq30952 (τ X0) (τ X1)
       grind)
    | exact resolve eq30952 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq31413 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31189 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq31189
    | (have j0 := eq31189 X0 X1
       grind)
    | exact resolve eq31189 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31189
  have eq31469 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31413 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31413
    | (have j0 := eq31413 X0 X1
       grind)
    | exact resolve eq31413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31413
  have eq31503 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31469 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq31469
    | (have j0 := eq31469 X0 X1
       grind)
    | exact resolve eq31469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31469
  have eq31536 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31503 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq31503
    | (have j0 := eq31503 X0 X1
       grind)
    | exact resolve eq31503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31503
  have eq31553 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31536 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31536
    | (have j0 := eq31536 X0 X1
       grind)
    | exact resolve eq31536 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31536
  have eq31602 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30952 X0 X1
       have i₂ := eq31553 X0 X1
       grind)
    | exact superpose eq31553 eq30952
    | (have j0 := eq30952 X0 X1
       have j1 := eq31553 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq30952 eq31553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30952 eq31553
  have eq33278 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq31602 x y
       grind)
    | exact superpose eq31602 eq16
    | (have j1 := eq31602 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq31602 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq31602 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq31602 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq31602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31602
  have eq33370 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq33278
  have eq33422 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq33370
       grind)
    | exact superpose eq33370 eq10
    | exact resolve eq10 eq33370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33370
  have eq33609 : x = y ∨ x = y := by
    first
    | (have i₁ := eq33422
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33422
    | exact resolve eq33422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33422
  have eq33610 : x = y := by grind
  clear eq33609
  have eq33613 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33610
       grind)
    | exact superpose eq33610 eq16
    | exact resolve eq16 eq33610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33610
  have eq33614 : False := by grind
  exact eq33614

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation837 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq81 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq81 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq81 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq198 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq199 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq205 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq206 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq525 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq206 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq206
    | exact resolve eq206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206 x y
       grind)
    | exact superpose eq206 eq16
    | (have j1 := eq206 x y
       grind)
    | exact resolve eq16 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq556 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq525
    | (have j0 := eq525 X0 X1
       grind)
    | exact resolve eq525 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq525
  have eq561 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq556 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq556
    | exact resolve eq556 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq667 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq532
       have i₂ := eq561 x y
       grind)
    | exact superpose eq561 eq532
    | (have j1 := eq561 (σ x) (σ y)
       grind)
    | (have r₁ := eq532
       have r₂ := eq561 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq532
       have r₂ := eq561 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq532 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq561
  have eq670 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq667
  have eq729 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq670
       grind)
    | exact superpose eq670 eq10
    | exact resolve eq10 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq766 : x = y ∨ x = y := by
    first
    | (have i₁ := eq729
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq729
    | exact resolve eq729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq767 : x = y := by grind
  clear eq766
  have eq769 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq767
       grind)
    | exact superpose eq767 eq16
    | exact resolve eq16 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq770 : False := by grind
  exact eq770

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation837 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq740 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
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
  have eq787 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq740 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq788 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq787 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq900 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq788 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq903 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq900 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq900 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq900 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq900 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq900 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq955 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq903 X0 (τ X1)
       grind)
    | exact superpose eq903 eq19
    | (have j1 := eq903 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq958 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq903 (σ X0) (σ X1)
       grind)
    | exact superpose eq903 eq15
    | (have j1 := eq903 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq1042 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq955
    | exact resolve eq955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1086 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1042 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1042
    | (have j0 := eq1042 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq1042 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1279 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq958 x y
       grind)
    | exact superpose eq958 eq16
    | (have j1 := eq958 x y
       grind)
    | exact resolve eq16 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1313 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1279
       have i₂ := eq1086 y x
       grind)
    | exact superpose eq1086 eq1279
    | (have j1 := eq1086 (σ x) (σ y)
       grind)
    | (have r₁ := eq1279
       have r₂ := eq1086 y x
       grind)
    | (have r₁ := eq1279
       have r₂ := eq1086 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1279
       have r₂ := eq1086 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1279 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq1279
  have eq1314 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1313
  have eq1318 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1314
       grind)
    | exact superpose eq1314 eq10
    | exact resolve eq10 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1362 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1318
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1318
    | exact resolve eq1318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1363 : x = y := by grind
  clear eq1362
  have eq1365 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1363
       grind)
    | exact superpose eq1363 eq16
    | exact resolve eq16 eq1363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1366 : False := by grind
  exact eq1366
