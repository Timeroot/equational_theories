import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_y_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq50 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq120 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  have eq131 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq120 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq120
    | exact resolve eq120 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq153 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq20 X0 X1 X2
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1 X0
       have i₂ := eq153 X1 X0 X2
       grind)
    | (have i₁ := eq20 (M.op X0 X2) X0 X1
       have i₂ := eq153 X0 X1 X2
       grind)
    | exact superpose eq153 eq20
    | exact resolve eq20 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X3) (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X0
       have i₂ := eq153 X1 X0 X2
       grind)
    | (have i₁ := eq9 (M.op (M.op X0 X2) X0) X1 X1
       have i₂ := eq153 X0 X1 X2
       grind)
    | exact superpose eq153 eq9
    | exact resolve eq9 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 X2 X0
       have i₂ := eq154 X1 X2 X0
       grind)
    | (have i₁ := eq20 X0 X1 X0
       have i₂ := eq154 X0 X1 X0
       grind)
    | exact superpose eq154 eq20
    | exact resolve eq20 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq153 (M.op X1 X2) X0 X3
       have i₂ := eq154 X1 X2 X0
       grind)
    | (have i₁ := eq153 (M.op X0 X1) X0 X2
       have i₂ := eq154 X0 X1 X0
       grind)
    | exact superpose eq154 eq153
    | exact resolve eq153 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq154 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq154 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq154 eq9
    | exact resolve eq9 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X0 (M.op (M.op X1 X2) X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq573 X3 X0 X1
       have i₂ := eq153 X1 X0 X2
       grind)
    | (have i₁ := eq573 X0 (M.op X0 X2) X0
       have i₂ := eq153 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq153 eq573
    | exact resolve eq573 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op (M.op X0 X1) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq573 X3 (M.op X0 X1) (M.op X2 X0)
       have i₂ := eq604 X0 X1 X2
       grind)
    | exact superpose eq604 eq573
    | exact resolve eq573 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq604 X0 x X1
       grind)
    | exact superpose eq604 eq9
    | exact resolve eq9 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq92
    | (have j0 := eq92 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq92 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq1668 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) = (M.op X0 (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq573 X3 X0 (M.op X0 (M.op (M.op X1 X2) X1))
       have i₂ := eq178 X0 X1 X2
       grind)
    | exact superpose eq178 eq573
    | exact resolve eq573 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2121 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op (M.op X1 X3) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 (M.op X0 (M.op (M.op X1 X3) X1)) X0
       have i₂ := eq624 X0 X1 X3 X2
       grind)
    | exact superpose eq624 eq20
    | exact resolve eq20 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq624
  have eq4915 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq10861 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X0 (M.op X1 X2))))) = (M.op X3 (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X2)) X4) (M.op X1 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2121 X0 (M.op X1 (M.op X1 X2)) X3 X4
       have i₂ := eq154 X1 X2 X0
       grind)
    | (have i₁ := eq2121 X2 (M.op X2 (M.op X0 X1)) X2 X3
       have i₂ := eq154 X0 X1 X2
       grind)
    | exact superpose eq154 eq2121
    | exact resolve eq2121 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq10985 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X0 X1)))) = (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2121 X0 (M.op X0 X1) X3 x
       have i₂ := eq1668 X0 X1 X2 (M.op (M.op X0 X1) x)
       grind)
    | (have i₁ := eq2121 (M.op (M.op (M.op X1 X2) X1) X3) (M.op (M.op X1 X2) X1) X2 X3
       have i₂ := eq1668 (M.op (M.op (M.op X1 X2) X1) X3) X1 X2 X3
       grind)
    | exact superpose eq1668 eq2121
    | exact resolve eq2121 eq1668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121
  have eq11491 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X0 (M.op X1 X2))))) = (M.op X3 (M.op X0 (M.op X1 (M.op X1 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10861 X0 X1 X2 X3 x
       have i₂ := eq575 X0 X1 (M.op X1 X2) x
       grind)
    | exact superpose eq575 eq10861
    | exact resolve eq10861 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq10861
  have eq16502 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4915 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4915
    | exact resolve eq4915 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915
  have eq16527 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq16502 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq16502
    | (have j0 := eq16502 X0
       grind)
    | exact resolve eq16502 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16502
  have eq16533 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq16527 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16527
    | (have j0 := eq16527 X0
       grind)
    | exact resolve eq16527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16527
  have eq16536 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16533 X0
       have j1 := eq50 X0
       grind)
    | (have r₁ := eq16533 X0
       have r₂ := eq50 X0
       grind)
    | exact resolve eq16533 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq16533
  have eq16580 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq16536 (σ X0)
       grind)
    | exact superpose eq16536 eq15
    | exact resolve eq15 eq16536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16582 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq16536 (τ X0)
       grind)
    | exact superpose eq16536 eq38
    | exact resolve eq38 eq16536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq16597 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16582 X0
       have i₂ := eq16536 X0
       grind)
    | exact superpose eq16536 eq16582
    | exact resolve eq16582 eq16536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16582
  have eq16599 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16580 X0
       have i₂ := eq16536 X0
       grind)
    | exact superpose eq16536 eq16580
    | exact resolve eq16580 eq16536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16536 eq16580
  have eq17039 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq16599 X0
       grind)
    | exact superpose eq16599 eq9
    | exact resolve eq9 eq16599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17067 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op X1 (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 (σ X0) (σ X0)
       have i₂ := eq16599 X0
       grind)
    | exact superpose eq16599 eq573
    | exact resolve eq573 eq16599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq17086 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 (σ X0) (σ X0) x
       have i₂ := eq16599 X0
       grind)
    | exact superpose eq16599 eq741
    | exact resolve eq741 eq16599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq17790 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq17039 X0 (σ X0)
       have i₂ := eq16599 X0
       grind)
    | exact superpose eq16599 eq17039
    | exact resolve eq17039 eq16599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18029 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17086 (M.op x (M.op x x)) X1
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq17086
    | exact resolve eq17086 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17086
  have eq19324 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq18029 X0 (σ X0)
       have i₂ := eq16599 X0
       grind)
    | exact superpose eq16599 eq18029
    | exact resolve eq18029 eq16599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19402 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17039 (M.op X0 (M.op X0 X0)) (M.op (σ X0) X1)
       have i₂ := eq18029 X0 X1
       grind)
    | exact superpose eq18029 eq17039
    | exact resolve eq17039 eq18029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17039 eq18029
  have eq19480 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19402 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq19402
    | exact resolve eq19402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19402
  have eq19513 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19480 X0 x
       have i₂ := eq153 (σ X0) (σ X0) x
       grind)
    | exact superpose eq153 eq19480
    | exact resolve eq19480 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq19480
  have eq19534 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19513 X0
       have i₂ := eq16599 X0
       grind)
    | exact superpose eq16599 eq19513
    | exact resolve eq19513 eq16599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19513
  have eq20434 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X1 X0))) (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq19324 (M.op x x)
       have i₂ := eq737 x x x x
       grind)
    | (have i₁ := eq19324 (M.op x x)
       have i₂ := eq737 x x x x
       grind)
    | exact superpose eq737 eq19324
    | exact resolve eq19324 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19324
  have eq20552 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X1 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20434 X0 X1
       have i₂ := eq604 X0 X0 X1
       grind)
    | exact superpose eq604 eq20434
    | exact resolve eq20434 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20434
  have eq20626 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X1 X0)))) = (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq19534 (M.op x x)
       have i₂ := eq737 x x x x
       grind)
    | (have i₁ := eq19534 (M.op x x)
       have i₂ := eq737 x x x x
       grind)
    | exact superpose eq737 eq19534
    | exact resolve eq19534 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20741 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq20626 X0 X1
       have i₂ := eq604 X0 X0 X1
       grind)
    | exact superpose eq604 eq20626
    | exact resolve eq20626 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20626
  have eq20897 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq811 x y
       grind)
    | exact superpose eq811 eq16
    | (have j1 := eq811 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq811 x y
       grind)
    | exact resolve eq16 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq20977 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq20897
  have eq21052 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20977
       have i₂ := eq16599 y
       grind)
    | exact superpose eq16599 eq20977
    | exact resolve eq20977 eq16599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20977
  have eq21177 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21052
       have i₂ := eq16599 x
       grind)
    | exact superpose eq16599 eq21052
    | exact resolve eq21052 eq16599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21052
  have eq21295 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21177
       have i₂ := eq16599 x
       grind)
    | exact superpose eq16599 eq21177
    | exact resolve eq21177 eq16599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21177
  have eq26747 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (M.op (M.op (M.op (σ X0) (σ (M.op X0 X0))) X2) (M.op (σ X0) (σ (M.op X0 X0))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0))) X2 x
       have i₂ := eq17790 X0
       grind)
    | exact superpose eq17790 eq180
    | exact resolve eq180 eq17790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq17790
  have eq27168 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq26747 X0 X1 x
       have i₂ := eq10985 (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0))) x (M.op (σ X0) X1)
       grind)
    | exact superpose eq10985 eq26747
    | exact resolve eq26747 eq10985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10985 eq26747
  have eq27262 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq27168 X0 X1
       have i₂ := eq11491 (σ (M.op X0 X0)) (σ X0) (σ (M.op X0 X0)) (M.op (σ X0) X1)
       grind)
    | exact superpose eq11491 eq27168
    | exact resolve eq27168 eq11491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11491 eq27168
  have eq27325 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27262 X0 X1
       have i₂ := eq17067 X0 (σ X0)
       grind)
    | exact superpose eq17067 eq27262
    | exact resolve eq27262 eq17067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17067 eq27262
  have eq27347 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27325 X0 X1
       have i₂ := eq16599 (M.op X0 X0)
       grind)
    | exact superpose eq16599 eq27325
    | exact resolve eq27325 eq16599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27325
  have eq29597 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X2) (σ (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27347 X0 X2
       have i₂ := eq737 X0 X0 X0 X1
       grind)
    | (have i₁ := eq27347 X0 X2
       have i₂ := eq737 X0 X0 X1 X0
       grind)
    | exact superpose eq737 eq27347
    | exact resolve eq27347 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq27347
  have eq33551 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (M.op (M.op (τ X0) (τ X0)) (M.op X1 (τ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20552 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20552
    | exact resolve eq20552 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20552
  have eq33722 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33551 X0 X1
       have i₂ := eq16597 X0
       grind)
    | exact superpose eq16597 eq33551
    | exact resolve eq33551 eq16597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33551
  have eq33820 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33722 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq33722
    | exact resolve eq33722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33722
  have eq35502 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ (M.op X0 X0))) (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq20741 (τ X0) X1
       have i₂ := eq16597 X0
       grind)
    | exact superpose eq16597 eq20741
    | exact resolve eq20741 eq16597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20741
  have eq35811 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq35502 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq35502
    | exact resolve eq35502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35502
  have eq35869 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35811 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35811
    | exact resolve eq35811 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35811
  have eq36576 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X0)) X1) (σ (M.op (τ (M.op X0 X0)) (M.op X2 (τ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29597 (τ X0) X2 X1
       have i₂ := eq16597 X0
       grind)
    | exact superpose eq16597 eq29597
    | exact resolve eq29597 eq16597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16597 eq29597
  have eq36886 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ (M.op (τ (M.op X0 X0)) (M.op X2 (τ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36576 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36576
    | exact resolve eq36576 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36576
  have eq38354 : ∀ X0 X1 X2 : G, (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X2 (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq604 (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) X0 X2
       have i₂ := eq33820 X0 X1
       grind)
    | exact superpose eq33820 eq604
    | exact resolve eq604 eq33820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33820
  have eq39243 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X3 X0)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) X2) (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1668 (M.op X0 X0) (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) X2 X3
       have i₂ := eq35869 X0 X1
       grind)
    | exact superpose eq35869 eq1668
    | exact resolve eq1668 eq35869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668 eq35869
  have eq39275 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) (M.op X3 X0)) = (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq39243 X0 X1 x X3
       have i₂ := eq38354 X0 X1 (M.op (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) x)
       grind)
    | exact superpose eq38354 eq39243
    | exact resolve eq39243 eq38354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38354 eq39243
  have eq196566 : (M.op x x) = (τ (σ y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq21295
       grind)
    | exact superpose eq21295 eq10
    | exact resolve eq10 eq21295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21295
  have eq196787 : y = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq196566
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq196566
    | exact resolve eq196566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196566
  have eq196788 : (σ (M.op y y)) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq196787
  have eq929682 : (M.op y y) = (τ (σ (M.op x x))) ∨ y = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq196788
       grind)
    | exact superpose eq196788 eq10
    | exact resolve eq10 eq196788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196788
  have eq930189 : (M.op y y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq929682
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq929682
    | exact resolve eq929682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929682
  have eq930190 : y = (M.op x x) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq930189
  have eq932675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq19534 x
       have i₂ := eq930190
       grind)
    | exact superpose eq930190 eq19534
    | exact resolve eq19534 eq930190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19534 eq930190
  have eq933180 : (M.op y y) = (M.op x x) := by
    first
    | (have r₁ := eq932675
       have r₂ := eq16
       grind)
    | exact resolve eq932675 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932675
  have eq933755 : ∀ X0 : G, y = (M.op (M.op x x) (σ (M.op (τ (M.op x x)) (M.op X0 (τ y))))) := by
    intro X0
    first
    | (have i₁ := eq36886 y y x
       have i₂ := eq933180
       grind)
    | exact superpose eq933180 eq36886
    | exact resolve eq36886 eq933180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36886
  have eq933761 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (σ (M.op (τ (M.op x x)) (M.op X0 (τ y)))) := by
    intro X0
    first
    | (have i₁ := eq39275 y x y
       have i₂ := eq933180
       grind)
    | exact superpose eq933180 eq39275
    | exact resolve eq39275 eq933180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39275 eq933180
  have eq933806 : y = (M.op (M.op x x) (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq933755 x
       have i₂ := eq933761 x
       grind)
    | exact superpose eq933761 eq933755
    | exact resolve eq933755 eq933761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933755 eq933761
  have eq933953 : x = y := by
    first
    | (have i₁ := eq933806
       have i₂ := eq604 x x x
       grind)
    | exact superpose eq604 eq933806
    | exact resolve eq933806 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq933806
  have eq934044 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq933953
       grind)
    | exact superpose eq933953 eq16
    | exact resolve eq16 eq933953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933953
  have eq934045 : False := by grind
  exact eq934045

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxx_pxy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq30 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X0) X2 (M.op X0 X1)
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) X0) (M.op X1 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    grind
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) (k (M.op X0 X0) X0))) := by
    intro X0
    grind
  have eq70 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq30 X0 X1 X2
       grind)
    | exact superpose eq30 eq30
    | exact resolve eq30 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq292 : ∀ X0 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq30 (M.op X0 X0) (k (M.op X0 X0) X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq30
    | exact resolve eq30 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq301 : ∀ X0 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq292 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq292
    | exact resolve eq292 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq345 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X2) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 (M.op X1 X2)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 X2 X0
       have i₂ := eq70 X1 X2 X0
       grind)
    | (have i₁ := eq30 X0 X1 X0
       have i₂ := eq70 X0 X1 X0
       grind)
    | exact superpose eq70 eq30
    | exact resolve eq30 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq70
  have eq418 : ∀ X1 : G, (M.op X1 X1) = (M.op (k (M.op X1 X1) X1) X1) := by
    intro X1
    first
    | (have i₁ := eq60 X1 (M.op X1 x)
       have i₂ := eq345 X1 X1 x
       grind)
    | exact superpose eq345 eq60
    | exact resolve eq60 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq345
  have eq516 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (k (M.op X1 X1) X1)) = (M.op (M.op (M.op (M.op X1 X1) (k (M.op X1 X1) X1)) X0) (k (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (k (M.op X1 X1) X1) X1 x
       have i₂ := eq418 X1
       grind)
    | exact superpose eq418 eq32
    | exact resolve eq32 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq418
  have eq531 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (M.op X1 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq516 X0 X0
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq516
    | exact resolve eq516 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq516
  have eq677 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) (k (M.op X0 X0) X0)))) := by
    intro X0 X1
    grind
  clear eq349
  have eq718 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 X1
       have i₂ := eq531 X0 X0
       grind)
    | exact superpose eq531 eq677
    | exact resolve eq677 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq2013 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq175 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq175 X0 X1
       grind)
    | exact superpose eq175 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq175 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq175 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq175 X0 X1
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2040 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2013 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2041 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2040 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2048 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2041 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2041
    | (have j0 := eq2041 X0 X1
       grind)
    | exact resolve eq2041 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041
  have eq2049 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2048 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq3858 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2049 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2049
    | exact resolve eq2049 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049
  have eq4066 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3858 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq3858
    | (have j0 := eq3858 X0 X1
       grind)
    | exact resolve eq3858 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3858
  have eq4074 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4066 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4066
    | exact resolve eq4066 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4180 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq4066 X0 X1
       grind)
    | exact superpose eq4066 eq10
    | (have j1 := eq4066 X0 X1
       grind)
    | exact resolve eq10 eq4066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4066
  have eq4319 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq718 X1 X1
       have i₂ := eq4074 X0 X1
       grind)
    | (have i₁ := eq718 X0 X1
       have i₂ := eq4074 (M.op X1 X0) X1
       grind)
    | exact superpose eq4074 eq718
    | (have j1 := eq4074 X0 X1
       grind)
    | exact resolve eq718 eq4074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq4830 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4319 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319
  have eq4949 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4830 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830
  have eq4968 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4949 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4949
    | exact resolve eq4949 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4979 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4968 X0
       have i₂ := eq4949 X0
       grind)
    | exact superpose eq4949 eq4968
    | exact resolve eq4968 eq4949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4949 eq4968
  have eq5093 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq531 X1 (σ X0)
       have i₂ := eq4979 X0
       grind)
    | exact superpose eq4979 eq531
    | exact resolve eq531 eq4979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq5139 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (k (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5093 X0 X1
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq5093
    | exact resolve eq5093 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5093
  have eq6409 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq5139 X0 (σ X0)
       have i₂ := eq4979 X0
       grind)
    | exact superpose eq4979 eq5139
    | exact resolve eq5139 eq4979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5139
  have eq7075 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (k X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq6409 (M.op x (M.op x x))
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq6409
    | exact resolve eq6409 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6409
  have eq7141 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7075 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq7075
    | exact resolve eq7075 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq7075
  have eq8324 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4180 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4180
    | (have j0 := eq4180 X1 (τ X0)
       grind)
    | exact resolve eq4180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4180
  have eq8359 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ X0)) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8324 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8324
    | (have j0 := eq8324 (σ X0) (σ X1)
       grind)
    | exact resolve eq8324 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8324
  have eq8459 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X1 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8359 X0 X1
       have i₂ := eq4979 X1
       grind)
    | exact superpose eq4979 eq8359
    | (have j0 := eq8359 X0 X1
       grind)
    | exact resolve eq8359 eq4979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4979 eq8359
  have eq8464 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8459 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq8459
    | (have j0 := eq8459 X0 X1
       grind)
    | exact resolve eq8459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8459
  have eq8467 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8464 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8464
    | (have j0 := eq8464 X0 X1
       grind)
    | exact resolve eq8464 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8464
  have eq9029 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8467 y x
       grind)
    | exact superpose eq8467 eq16
    | (have j1 := eq8467 y x
       grind)
    | exact resolve eq16 eq8467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8467
  have eq9104 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9029
       have i₂ := eq4074 y x
       grind)
    | exact superpose eq4074 eq9029
    | (have j1 := eq4074 y x
       grind)
    | exact resolve eq9029 eq4074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4074 eq9029
  have eq9107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq9104
  have eq9108 : y = (M.op x x) := by grind
  clear eq9107
  have eq9147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7141 x
       have i₂ := eq9108
       grind)
    | exact superpose eq9108 eq7141
    | exact resolve eq7141 eq9108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7141 eq9108
  have eq9196 : False := by grind
  exact eq9196

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq52 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq63 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq139 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq674 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq675 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq674 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq680 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq675 X0 X1
       have j1 := eq139 X0 X1
       grind)
    | (have r₁ := eq675 X0 X1
       have r₂ := eq139 X0 X1
       grind)
    | (have r₁ := eq675 X1 X1
       have r₂ := eq139 X1 X1
       grind)
    | exact resolve eq675 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq675
  have eq1251 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq680 (σ X1) (σ X0)
       grind)
    | exact superpose eq680 eq15
    | exact resolve eq15 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1254 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1251 X0 X1
       have i₂ := eq680 X1 X0
       grind)
    | exact superpose eq680 eq1251
    | exact resolve eq1251 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq1251
  have eq1258 : False := by grind
  exact eq1258

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq77 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq94 y x
       grind)
    | exact superpose eq94 eq73
    | (have j1 := eq94 y x
       grind)
    | exact resolve eq73 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120 eq94
    | (have j0 := eq94 (σ y) (σ x)
       grind)
    | exact resolve eq94 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq77
    | (have r₁ := eq77
       have r₂ := eq129
       grind)
    | exact resolve eq77 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq129
  have eq523 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq522
  have eq544 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq523 eq120
    | exact resolve eq120 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq548 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq544
  have eq553 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq548
       have r₂ := eq131
       grind)
    | exact resolve eq548 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq548
  have eq612 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq553 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq553
       grind)
    | exact resolve eq13 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq617 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq612 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq617 eq120
    | exact resolve eq120 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq617
  have eq711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq708
  have eq716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq711
    | exact resolve eq711 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq718 : x = (M.op x y) := by
    first
    | (have r₁ := eq716
       have r₂ := eq27
       grind)
    | exact resolve eq716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq720 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq718 eq20
    | exact resolve eq20 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq718 eq76
    | (have r₁ := eq76
       have r₂ := eq718
       grind)
    | exact resolve eq76 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq718
  have eq729 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq725
  have eq735 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq720
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq720
    | exact resolve eq720 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq736 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq735 eq26
    | exact resolve eq26 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1107 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq729
       grind)
    | exact superpose eq729 eq73
    | exact resolve eq73 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq1114 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq735 eq1107
    | exact resolve eq1107 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1116 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1114
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1114
    | exact resolve eq1114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1114
  have eq1117 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq735 eq1116
    | exact resolve eq1116 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1150 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1117 eq94
    | (have j0 := eq94 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq94 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1151 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1150
  have eq1153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq736 eq1151
    | exact resolve eq1151 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1156 : x = (M.op x x) := by
    first
    | (have r₁ := eq1153
       have r₂ := eq27
       grind)
    | exact resolve eq1153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1167 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1156
       grind)
    | exact superpose eq1156 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1156
       grind)
    | exact resolve eq13 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1176 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1167 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1243 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1176 y
       grind)
    | exact superpose eq1176 eq73
    | exact resolve eq73 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1176
  have eq1248 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq735 eq1243
    | exact resolve eq1243 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq1243
  have eq1252 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1248
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1248
    | exact resolve eq1248 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1248
  have eq1255 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1252
    | exact resolve eq1252 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1252
  have eq1262 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1255 eq94
    | (have j0 := eq94 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq94 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1255
  have eq1263 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1262
  have eq1265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq736 eq1263
    | exact resolve eq1263 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq1263
  have eq1268 : False := by grind
  exact eq1268

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pxy_Equation1469 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
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
  have eq42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq105 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq100
    | (have j0 := eq100 X0 X1
       grind)
    | exact resolve eq100 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq105
    | (have j0 := eq105 X0 X1
       grind)
    | exact resolve eq105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq142 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op X1 (M.op X1 (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) (σ X0) x
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq42
    | exact resolve eq42 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq42 X0 X1 X2
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X1 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X0 X1 X0
       have i₂ := eq145 X1 X0 X2
       grind)
    | (have i₁ := eq42 (M.op X0 X2) X0 X1
       have i₂ := eq145 X0 X1 X2
       grind)
    | exact superpose eq145 eq42
    | exact resolve eq42 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X1 X2 X0
       have i₂ := eq144 X1 X2 X0
       grind)
    | (have i₁ := eq42 X0 X1 X0
       have i₂ := eq144 X0 X1 X0
       grind)
    | exact superpose eq144 eq42
    | exact resolve eq42 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq602 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq144 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq144 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq144 eq9
    | exact resolve eq9 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq618 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109 x y
       grind)
    | exact superpose eq109 eq16
    | (have j1 := eq109 x y
       grind)
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq840 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op (M.op X0 X1) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq571 X3 (M.op X0 X1) (M.op X2 X0)
       have i₂ := eq602 X0 X1 X2
       grind)
    | exact superpose eq602 eq571
    | exact resolve eq571 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq602 X0 x X1
       grind)
    | exact superpose eq602 eq9
    | exact resolve eq9 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq885 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq844 (σ X0) (σ X0) x
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq844
    | exact resolve eq844 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1094 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq885 (M.op x (M.op x x)) X1
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq885
    | exact resolve eq885 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq1251 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1094 X0 (M.op x (M.op x (σ (M.op X0 X0))))
       have i₂ := eq142 X0 x
       grind)
    | exact superpose eq142 eq1094
    | exact resolve eq1094 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq1269 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op X0 (M.op X0 X0)) (M.op (σ X0) X1)
       have i₂ := eq1094 X0 X1
       grind)
    | exact superpose eq1094 eq49
    | exact resolve eq49 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1094
  have eq1290 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op (σ X0) X1) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1269 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq1269
    | exact resolve eq1269 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1297 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1290 X0 x
       have i₂ := eq145 (σ X0) (σ X0) x
       grind)
    | exact superpose eq145 eq1290
    | exact resolve eq1290 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq1290
  have eq1300 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1297 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1297
    | exact resolve eq1297 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq2811 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) = (M.op X0 (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq571 X3 X0 (M.op X0 (M.op (M.op X1 X2) X1))
       have i₂ := eq160 X0 X1 X2
       grind)
    | exact superpose eq160 eq571
    | exact resolve eq571 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq571
  have eq4134 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq618
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq618
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq618
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq618
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq618 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq4135 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4134
  have eq4438 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X1 X0))) (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1251 (M.op x x)
       have i₂ := eq840 x x x x
       grind)
    | (have i₁ := eq1251 (M.op x x)
       have i₂ := eq840 x x x x
       grind)
    | exact superpose eq840 eq1251
    | exact resolve eq1251 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq4440 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X1 X0)))) = (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1300 (M.op x x)
       have i₂ := eq840 x x x x
       grind)
    | (have i₁ := eq1300 (M.op x x)
       have i₂ := eq840 x x x x
       grind)
    | exact superpose eq840 eq1300
    | exact resolve eq1300 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq1300
  have eq4477 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4440 X0 X1
       have i₂ := eq602 X0 X0 X1
       grind)
    | exact superpose eq602 eq4440
    | exact resolve eq4440 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4440
  have eq4478 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X1 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4438 X0 X1
       have i₂ := eq602 X0 X0 X1
       grind)
    | exact superpose eq602 eq4438
    | exact resolve eq4438 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4438
  have eq7772 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ (M.op X0 X0))) (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4477 (τ X0) X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq4477
    | exact resolve eq4477 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7892 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X2) (σ (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq844 (σ (M.op (M.op X0 X0) (M.op X1 X0))) (σ (M.op X0 X0)) X2
       have i₂ := eq4477 X0 X1
       grind)
    | exact superpose eq4477 eq844
    | exact resolve eq844 eq4477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq4477
  have eq7943 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq7772 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq7772
    | exact resolve eq7772 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7772
  have eq7979 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7943 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7943
    | exact resolve eq7943 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq8276 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (M.op (M.op (τ X0) (τ X0)) (M.op X1 (τ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4478 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4478
    | exact resolve eq4478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478
  have eq8366 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8276 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq8276
    | exact resolve eq8276 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8276
  have eq8416 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8366 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq8366
    | exact resolve eq8366 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8366
  have eq9927 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X0)) X1) (σ (M.op (τ (M.op X0 X0)) (M.op X2 (τ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7892 (τ X0) X2 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq7892
    | exact resolve eq7892 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq7892
  have eq10110 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ (M.op (τ (M.op X0 X0)) (M.op X2 (τ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9927 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9927
    | exact resolve eq9927 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9927
  have eq10474 : ∀ X0 X1 X2 : G, (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X2 (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq602 (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) X0 X2
       have i₂ := eq8416 X0 X1
       grind)
    | exact superpose eq8416 eq602
    | exact resolve eq602 eq8416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8416
  have eq26101 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X3 X0)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) X2) (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2811 (M.op X0 X0) (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) X2 X3
       have i₂ := eq7979 X0 X1
       grind)
    | exact superpose eq7979 eq2811
    | exact resolve eq2811 eq7979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811 eq7979
  have eq26803 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) (M.op X3 X0)) = (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq26101 X0 X1 x X3
       have i₂ := eq10474 X0 X1 (M.op (σ (M.op (τ (M.op X0 X0)) (M.op X1 (τ X0)))) x)
       grind)
    | exact superpose eq10474 eq26101
    | exact resolve eq26101 eq10474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10474 eq26101
  have eq106014 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4135
       grind)
    | exact superpose eq4135 eq16
    | exact resolve eq16 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135
  have eq106015 : (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq106014
       have r₂ := eq22 x
       grind)
    | exact resolve eq106014 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106014
  have eq709724 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq106015
       grind)
    | exact superpose eq106015 eq22
    | exact resolve eq22 eq106015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106015
  have eq710003 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq709724
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq709724
    | exact resolve eq709724 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709724
  have eq710004 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq710003
  have eq711607 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq710004
       grind)
    | exact superpose eq710004 eq10
    | exact resolve eq10 eq710004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710004
  have eq711960 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq711607
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq711607
    | exact resolve eq711607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711607
  have eq711961 : (M.op x x) = (M.op y y) := by grind
  clear eq711960
  have eq712520 : ∀ X0 : G, y = (M.op (M.op x x) (σ (M.op (τ (M.op x x)) (M.op X0 (τ y))))) := by
    intro X0
    first
    | (have i₁ := eq10110 y y x
       have i₂ := eq711961
       grind)
    | exact superpose eq711961 eq10110
    | exact resolve eq10110 eq711961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10110
  have eq712558 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (σ (M.op (τ (M.op x x)) (M.op X0 (τ y)))) := by
    intro X0
    first
    | (have i₁ := eq26803 y x y
       have i₂ := eq711961
       grind)
    | exact superpose eq711961 eq26803
    | exact resolve eq26803 eq711961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26803 eq711961
  have eq712615 : y = (M.op (M.op x x) (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq712520 x
       have i₂ := eq712558 x
       grind)
    | exact superpose eq712558 eq712520
    | exact resolve eq712520 eq712558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712520 eq712558
  have eq712778 : x = y := by
    first
    | (have i₁ := eq712615
       have i₂ := eq602 x x x
       grind)
    | exact superpose eq602 eq712615
    | exact resolve eq712615 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq712615
  have eq713379 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq712778
       grind)
    | exact superpose eq712778 eq16
    | exact resolve eq16 eq712778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712778
  have eq713380 : False := by grind
  exact eq713380

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyy_pyx_Equation1469 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq34
  have eq46 : x = (τ (σ x)) := by
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
  have eq47 : y = (τ (σ y)) := by
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
  have eq63 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 y X0 x
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ y) X0 (σ x)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq104 : ∀ X1 : G, (M.op x y) = (M.op x (M.op X1 (M.op X1 (M.op x y)))) := by
    intro X1
    first
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X1 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X1
    first
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq80
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq80 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq190 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq188
    | exact resolve eq188 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq194 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq190
    | exact resolve eq190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq370 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq104 eq64
    | exact resolve eq64 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq372 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq111 eq64
    | exact resolve eq64 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq111
  have eq561 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X1) (M.op X0 (M.op x (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq370 eq9
    | exact resolve eq9 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq600 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq372 eq9
    | exact resolve eq9 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq695 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq65 eq561
    | exact resolve eq561 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq736 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq68 eq600
    | exact resolve eq600 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq3332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq194
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq194
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq194 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq3352 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3332
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3332
    | exact resolve eq3332 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332
  have eq3355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq3352
    | exact resolve eq3352 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq3356 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq3355
       have r₂ := eq28
       grind)
    | exact resolve eq3355 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq3357 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3356
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3356
    | exact resolve eq3356 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356
  have eq3359 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3357 eq68
    | exact resolve eq68 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq3361 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3357 eq69
    | exact resolve eq69 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq3362 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3357 eq9
    | exact resolve eq9 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3386 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3359 eq736
    | exact resolve eq736 eq3359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq3359
  have eq4206 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3386 eq3362
    | exact resolve eq3362 eq3386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362 eq3386
  have eq4229 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4206
  have eq4235 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4229 eq3361
    | exact resolve eq3361 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3361 eq4229
  have eq4253 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4235
  have eq4575 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq4253
       grind)
    | exact superpose eq4253 eq65
    | exact resolve eq65 eq4253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq4577 : x = (M.op (M.op x y) (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq4253
       grind)
    | exact superpose eq4253 eq63
    | exact resolve eq63 eq4253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq4578 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op X0 y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq4253
       grind)
    | exact superpose eq4253 eq9
    | exact resolve eq9 eq4253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253
  have eq4600 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4575 eq695
    | exact resolve eq695 eq4575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq4575
  have eq4828 : y = (M.op (M.op x y) (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4578 y
       have i₂ := eq4600
       grind)
    | exact superpose eq4600 eq4578
    | exact resolve eq4578 eq4600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578 eq4600
  have eq4855 : y = (M.op (M.op x y) (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4828
  have eq4861 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4855 eq4577
    | exact resolve eq4577 eq4855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4577 eq4855
  have eq4881 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq4861
  have eq4889 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq4881 eq47
    | exact resolve eq47 eq4881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq4881
  have eq4926 : x = y ∨ x = y := by
    first
    | exact superpose eq46 eq4889
    | exact resolve eq4889 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq4889
  have eq4927 : x = y := by grind
  clear eq4926
  have eq4931 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq4927
       grind)
    | exact superpose eq4927 eq19
    | exact resolve eq19 eq4927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4932 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq4927
       grind)
    | exact superpose eq4927 eq25
    | exact resolve eq25 eq4927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4927
  have eq5318 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4932
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4932
    | exact resolve eq4932 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4932
  have eq5411 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5318 eq27
    | exact resolve eq27 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5318
  have eq5882 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq4931
       grind)
    | exact superpose eq4931 eq35
    | exact resolve eq35 eq4931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4931
  have eq5899 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5882
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5882
    | exact resolve eq5882 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5882
  have eq5957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5411 eq5899
    | exact resolve eq5899 eq5411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5411 eq5899
  have eq5969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq5957
    | exact resolve eq5957 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq5957
  have eq5974 : False := by grind
  exact eq5974

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyy_pyx_pxy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq45 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq105 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq10
    | exact resolve eq10 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq169 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
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
  have eq199 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X2 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1 X2
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq9
    | exact resolve eq9 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq169
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq169
    | exact resolve eq169 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq849 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq848
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq848
    | exact resolve eq848 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq945 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq849
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq849
    | (have j1 := eq59 x y
       grind)
    | exact resolve eq849 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq849
  have eq946 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq945
  have eq1190 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1 (τ X0)
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq199
    | exact resolve eq199 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq199
  have eq7764 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq946
       grind)
    | exact superpose eq946 eq10
    | exact resolve eq10 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq7819 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq7764
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq7764
    | exact resolve eq7764 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7764
  have eq7820 : (M.op x x) = (M.op y y) := by grind
  clear eq7819
  have eq7841 : ∀ X0 : G, (τ y) = (M.op (τ (M.op x x)) (M.op X0 (τ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq1190 y x
       have i₂ := eq7820
       grind)
    | exact superpose eq7820 eq1190
    | exact resolve eq1190 eq7820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7820
  have eq7893 : (τ y) = (τ x) := by
    first
    | (have i₁ := eq7841 x
       have i₂ := eq1190 x x
       grind)
    | exact superpose eq1190 eq7841
    | exact resolve eq7841 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq7841
  have eq7971 : y = (σ (τ x)) := by
    first
    | (have i₁ := eq11 y
       have i₂ := eq7893
       grind)
    | exact superpose eq7893 eq11
    | exact resolve eq11 eq7893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7893
  have eq8028 : x = y := by
    first
    | (have i₁ := eq7971
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq7971
    | exact resolve eq7971 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7971
  have eq8109 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8028
       grind)
    | exact superpose eq8028 eq16
    | exact resolve eq16 eq8028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8028
  have eq8110 : False := by grind
  exact eq8110

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_pyx_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
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
  have eq50 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 X1 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X1 (M.op X2 X0)) X3 X4 (M.op X0 x)
       have i₂ := eq14 X0 x X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X2) ≠ X0 ∨ (M.op X2 (M.op X0 (M.op X1 X0))) = (k X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op X1 X0))
       have i₂ := eq14 X0 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op X1 X0))
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
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
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
  clear eq43
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
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq72
    | exact resolve eq72 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq44
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq44 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq107 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq108 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq112 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq70 sF3
       grind)
    | exact superpose eq70 eq108
    | exact resolve eq108 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq114 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq112
    | exact resolve eq112 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq107
    | (have j1 := eq81 y x
       grind)
    | exact resolve eq107 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq122 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
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
  have eq136 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq16
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq155 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq152
       have i₂ := eq70 sF1
       grind)
    | exact superpose eq70 eq152
    | exact resolve eq152 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq157 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq155
       have i₂ := eq70 sF0
       grind)
    | exact superpose eq70 eq155
    | exact resolve eq155 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq252 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq253 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq101 eq81
    | (have j0 := eq81 (σ x) (σ y)
       grind)
    | exact resolve eq81 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq807
    | exact resolve eq807 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq811 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq808
       have r₂ := eq27
       grind)
    | exact resolve eq808 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq871 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X2 X4 (M.op (M.op X0 (M.op X1 X2)) x)
       have i₂ := eq55 X2 X0 X1 x X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq905 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq811 eq54
    | exact resolve eq54 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq907 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq811 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq811
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq811
       grind)
    | exact resolve eq12 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq811 eq56
    | exact resolve eq56 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq914 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq907
  have eq1112 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) = (k (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 (M.op X0 (M.op X1 X2)) X3 (M.op X4 X2)
       have i₂ := eq55 X2 X0 X1 (M.op X3 (M.op X0 (M.op X1 X2))) X4
       grind)
    | exact superpose eq55 eq69
    | (have j0 := eq69 (M.op X0 (M.op X1 X2)) X3 (M.op X4 X2)
       grind)
    | (have r₁ := eq69 (M.op X1 (M.op X2 X0)) X1 (M.op X4 X0)
       have r₂ := eq55 X0 X1 X2 (M.op X1 (M.op X1 (M.op X2 X0))) X4
       grind)
    | exact resolve eq69 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1116 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) (M.op (σ y) (M.op X0 (σ y)))) = (k (σ x) (M.op (σ y) (M.op X0 (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq913 eq69
    | (have j0 := eq69 (σ y) X0 (σ x)
       grind)
    | (have r₁ := eq69 (σ y) x (σ x)
       have r₂ := eq913 (M.op x (σ y))
       grind)
    | exact resolve eq69 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq1124 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 (σ y)))) = (k (σ x) (M.op (σ y) (M.op X0 (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1116 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1128 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) = (k (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq1112 X0 X1 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1132 : (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq591 eq1124
    | (have j0 := eq1124 (σ x)
       grind)
    | exact resolve eq1124 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1305 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq914 eq101
    | exact resolve eq101 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1306 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq914 eq60
    | exact resolve eq60 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq914
  have eq1308 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1305
  have eq1310 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq1306
    | exact resolve eq1306 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1315 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1308 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1337 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1315 X0
       have j1 := eq81 X0 (σ y)
       grind)
    | (have r₁ := eq1315 X0
       have r₂ := eq81 X0 (σ y)
       grind)
    | exact resolve eq1315 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1635 : (τ (σ y)) = (M.op y y) ∨ y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1310 eq136
    | exact resolve eq136 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq1310
  have eq1666 : y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq1635
    | exact resolve eq1635 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq1904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1337 eq101
    | exact resolve eq101 eq1337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1904
  have eq1914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq1908
    | exact resolve eq1908 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908
  have eq1916 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1914
       have r₂ := eq27
       grind)
    | exact resolve eq1914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914
  have eq1918 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq1916
       grind)
    | exact superpose eq1916 eq53
    | exact resolve eq53 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1919 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq1916
       grind)
    | exact superpose eq1916 eq50
    | exact resolve eq50 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1920 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1916
       grind)
    | exact superpose eq1916 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq1916
       grind)
    | exact resolve eq12 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1926 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56 x y x
       have i₂ := eq1916
       grind)
    | exact superpose eq1916 eq56
    | exact resolve eq56 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1933 : y = (k x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1920
  have eq1940 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1919 x
       have i₂ := eq590 sF0 x
       grind)
    | (have i₁ := eq1919 x
       have i₂ := eq590 sF0 x
       grind)
    | exact superpose eq590 eq1919
    | (have j0 := eq1919 x
       grind)
    | exact resolve eq1919 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq1942 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1940 eq157
    | exact resolve eq157 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq1961 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1942
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1942
    | exact resolve eq1942 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942
  have eq1965 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq1961 eq14
    | exact resolve eq14 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1970 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1961 eq56
    | exact resolve eq56 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2024 : ∀ X0 : G, y ≠ y ∨ (M.op x (M.op y (M.op X0 y))) = (k x (M.op y (M.op X0 y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq69 y X0 x
       have i₂ := eq1926 (M.op X0 y)
       grind)
    | exact superpose eq1926 eq69
    | (have j0 := eq69 y X0 x
       grind)
    | (have r₁ := eq69 y x x
       have r₂ := eq1926 (M.op x y)
       grind)
    | exact resolve eq69 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq2039 : ∀ X0 : G, (M.op x (M.op y (M.op X0 y))) = (k x (M.op y (M.op X0 y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2047 : (M.op x (M.op y (M.op x y))) = (k x (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2039 x
       have i₂ := eq590 y x
       grind)
    | (have i₁ := eq2039 x
       have i₂ := eq590 y x
       grind)
    | exact superpose eq590 eq2039
    | (have j0 := eq2039 x
       grind)
    | exact resolve eq2039 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq2111 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq1970
    | (have j0 := eq1970 (σ y)
       grind)
    | exact resolve eq1970 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970
  have eq2188 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (σ x)))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq1961 eq871
    | exact resolve eq871 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2755 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1961 eq1965
    | exact resolve eq1965 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq2787 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2755 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755
  have eq3412 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1933
       grind)
    | exact superpose eq1933 eq44
    | exact resolve eq44 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933
  have eq3414 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3412
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3412
    | exact resolve eq3412 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412
  have eq3421 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3414 eq81
    | (have j0 := eq81 (σ x) (σ y)
       grind)
    | exact resolve eq81 eq3414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3414
  have eq3426 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq3421
    | exact resolve eq3421 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq14986 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) X2)) = (k (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1128 X0 X1 X2 X4 X4
       have i₂ := eq871 X0 X1 X2 (M.op X0 (M.op X1 X2)) X4
       grind)
    | exact superpose eq871 eq1128
    | exact resolve eq1128 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871 eq1128
  have eq15477 : ∀ X0 : G, (M.op (M.op X0 x) y) = (k (M.op X0 x) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14986 y x x x
       have i₂ := eq1926 (M.op x x)
       grind)
    | exact superpose eq1926 eq14986
    | exact resolve eq14986 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq15478 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (k (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq253 eq14986
    | exact resolve eq14986 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14986
  have eq20803 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq1916
       grind)
    | exact superpose eq1916 eq122
    | exact resolve eq122 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq1916
  have eq20849 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20803
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20803
    | exact resolve eq20803 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20803
  have eq20853 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20849 eq81
    | (have j0 := eq81 (σ x) (σ y)
       grind)
    | exact resolve eq81 eq20849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20849
  have eq20867 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq20853
    | exact resolve eq20853 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20853
  have eq21079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20867 eq2787
    | exact resolve eq2787 eq20867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20867
  have eq21127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21079
  have eq21155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq21127
    | exact resolve eq21127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21127
  have eq21164 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21155
       have r₂ := eq27
       grind)
    | exact resolve eq21155 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21155
  have eq21167 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq21164 eq54
    | exact resolve eq54 eq21164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq21164
  have eq23129 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21167 eq2188
    | exact resolve eq2188 eq21167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188 eq21167
  have eq23183 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23129 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23129
  have eq23240 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq23183
    | (have j0 := eq23183 (σ x)
       grind)
    | exact resolve eq23183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23183
  have eq23437 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23240 eq1965
    | exact resolve eq1965 eq23240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1965 eq23240
  have eq23476 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23437 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23437
  have eq27504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3426 eq2787
    | exact resolve eq2787 eq3426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426
  have eq27561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq27504
  have eq27595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq27561
    | exact resolve eq27561 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27561
  have eq27604 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq27595
       have r₂ := eq27
       grind)
    | exact resolve eq27595 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27595
  have eq27613 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq590 X0 y
       have i₂ := eq27604
       grind)
    | exact superpose eq27604 eq590
    | exact resolve eq590 eq27604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27604
  have eq27903 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq27613 eq1918
    | exact resolve eq1918 eq27613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918 eq27613
  have eq28076 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq27903 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27903
  have eq28115 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28076 x
       have i₂ := eq590 y x
       grind)
    | (have i₁ := eq28076 x
       have i₂ := eq590 y x
       grind)
    | exact superpose eq590 eq28076
    | (have j0 := eq28076 x
       grind)
    | exact resolve eq28076 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28076
  have eq28303 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28115 eq2047
    | exact resolve eq2047 eq28115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047 eq28115
  have eq28394 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28303
  have eq28421 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28394
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28394
    | exact resolve eq28394 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28394
  have eq28520 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq28421
       grind)
    | exact superpose eq28421 eq44
    | exact resolve eq44 eq28421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28421
  have eq28556 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq28520
    | exact resolve eq28520 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28520
  have eq28713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28556 eq81
    | (have j0 := eq81 (σ x) (σ y)
       grind)
    | exact resolve eq81 eq28556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28556
  have eq28735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28713
    | exact resolve eq28713 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28713
  have eq28738 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28735
       have r₂ := eq27
       grind)
    | exact resolve eq28735 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28735
  have eq28759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28738 eq2787
    | exact resolve eq2787 eq28738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2787 eq28738
  have eq28816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28759
  have eq28848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28816
    | exact resolve eq28816 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28816
  have eq28859 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq28848
       have r₂ := eq27
       grind)
    | exact resolve eq28848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28848
  have eq28868 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op X1 (σ y)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq28859 eq252
    | exact resolve eq252 eq28859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28889 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28859 eq2111
    | exact resolve eq2111 eq28859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111 eq28859
  have eq28958 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq28889
  have eq28985 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq591 eq28868
    | (have j0 := eq28868 X0 (σ x)
       grind)
    | exact resolve eq28868 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28868
  have eq29733 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28985 eq23476
    | exact resolve eq23476 eq28985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23476 eq28985
  have eq29790 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq29733
  have eq29830 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29790 eq29
    | exact resolve eq29 eq29790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29832 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29790 eq40
    | exact resolve eq40 eq29790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq29790
  have eq29913 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq29832
    | exact resolve eq29832 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq29832
  have eq29915 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq29830
    | exact resolve eq29830 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29830
  have eq30014 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29915 eq50
    | exact resolve eq50 eq29915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq30015 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29915 eq53
    | exact resolve eq53 eq29915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30030 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29915 eq253
    | exact resolve eq253 eq29915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq30081 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq29915
  have eq30110 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30015 X0 x
       have i₂ := eq590 (M.op y X0) x
       grind)
    | (have i₁ := eq30015 X0 x
       have i₂ := eq590 (M.op y X0) x
       grind)
    | exact superpose eq590 eq30015
    | (have j0 := eq30015 X0 x
       grind)
    | exact resolve eq30015 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30015
  have eq33205 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15478 (M.op y x)
       have i₂ := eq30030 x
       grind)
    | exact superpose eq30030 eq15478
    | exact resolve eq15478 eq30030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15478 eq30030
  have eq43313 : (σ (k y y)) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33205 eq29913
    | exact resolve eq29913 eq33205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29913 eq33205
  have eq43418 : (σ (k y y)) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq43313
  have eq43494 : (σ (M.op y y)) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43418
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq43418
    | exact resolve eq43418 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43418
  have eq43509 : (M.op (σ y) (σ y)) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43494
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq43494
    | exact resolve eq43494 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq43494
  have eq43807 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43509 eq77
    | exact resolve eq77 eq43509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq43509
  have eq43881 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53 eq43807
    | exact resolve eq43807 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq43807
  have eq43890 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq591 eq43881
    | exact resolve eq43881 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43881
  have eq43892 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43890
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43890
    | exact resolve eq43890 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq43890
  have eq43917 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq43892 eq252
    | exact resolve eq252 eq43892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq43892
  have eq44017 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq591 eq43917
    | (have j0 := eq43917 (σ x)
       grind)
    | exact resolve eq43917 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq43917
  have eq44043 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44017 eq905
    | exact resolve eq905 eq44017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq44017
  have eq272395 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44043 eq1132
    | exact resolve eq1132 eq44043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq44043
  have eq272670 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq272395
  have eq272725 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq272670
    | exact resolve eq272670 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272670
  have eq292751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq272725 eq101
    | exact resolve eq101 eq272725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq272725
  have eq292800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq292751
  have eq292823 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq292800
       have r₂ := eq27
       grind)
    | exact resolve eq292800 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292800
  have eq292835 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30110 x
       have i₂ := eq292823
       grind)
    | exact superpose eq292823 eq30110
    | exact resolve eq30110 eq292823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30110
  have eq292857 : ∀ X0 : G, x = (M.op y (M.op X0 y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30014 X0 y
       have i₂ := eq292823
       grind)
    | exact superpose eq292823 eq30014
    | exact resolve eq30014 eq292823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30014 eq292823
  have eq292903 : ∀ X0 : G, x = (M.op y (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq292857 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292857
  have eq292906 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq292835
  have eq292930 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq292903 x
       have i₂ := eq590 y x
       grind)
    | (have i₁ := eq292903 x
       have i₂ := eq590 y x
       grind)
    | exact superpose eq590 eq292903
    | (have j0 := eq292903 x
       grind)
    | exact resolve eq292903 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq292903
  have eq294863 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq292930 eq292906
    | exact resolve eq292906 eq292930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292906 eq292930
  have eq294994 : x = y ∨ x = (M.op x y) := by grind
  clear eq294863
  have eq295040 : x = (M.op x y) := by
    first
    | (have r₁ := eq294994
       have r₂ := eq30081
       grind)
    | exact resolve eq294994 eq30081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30081 eq294994
  have eq295062 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq295040 eq20
    | exact resolve eq20 eq295040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq295150 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq295040 eq1940
    | exact resolve eq1940 eq295040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq295451 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq295062
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq295062
    | exact resolve eq295062 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295062
  have eq295482 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq295451 eq26
    | exact resolve eq26 eq295451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq297473 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15477 x
       have i₂ := eq295150
       grind)
    | exact superpose eq295150 eq15477
    | exact resolve eq15477 eq295150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15477 eq295150
  have eq297534 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq297473
  have eq297560 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq297534
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq297534
    | exact resolve eq297534 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq297534
  have eq297606 : x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq295040 eq297560
    | exact resolve eq297560 eq295040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297560
  have eq298592 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq297606
       grind)
    | exact superpose eq297606 eq44
    | exact resolve eq44 eq297606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq297606
  have eq298683 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq295451 eq298592
    | exact resolve eq298592 eq295451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298592
  have eq298719 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq298683
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq298683
    | exact resolve eq298683 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298683
  have eq298751 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq295451 eq298719
    | exact resolve eq298719 eq295451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298719
  have eq300376 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq298751 eq81
    | (have j0 := eq81 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq81 eq298751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq298751
  have eq300402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq295482 eq300376
    | exact resolve eq300376 eq295482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300376
  have eq300407 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq300402
       have r₂ := eq27
       grind)
    | exact resolve eq300402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300402
  have eq300779 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq300407 eq28958
    | exact resolve eq28958 eq300407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28958 eq300407
  have eq300960 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq300779
  have eq300998 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq295451 eq300960
    | exact resolve eq300960 eq295451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300960
  have eq300999 : (σ (M.op x y)) = (σ y) := by grind
  clear eq300998
  have eq301022 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq300999 eq29
    | exact resolve eq29 eq300999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq301470 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq300999 eq295482
    | exact resolve eq295482 eq300999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295482 eq300999
  have eq301540 : y = (M.op x y) := by
    first
    | exact superpose eq30 eq301022
    | exact resolve eq301022 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq301022
  have eq301591 : x = y := by
    first
    | exact superpose eq295040 eq301540
    | exact resolve eq301540 eq295040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295040 eq301540
  have eq301697 : x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1666
       have i₂ := eq301591
       grind)
    | exact superpose eq301591 eq1666
    | exact resolve eq1666 eq301591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666 eq301591
  have eq301970 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq301697
  have eq302067 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq301970
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq301970
    | exact resolve eq301970 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq301970
  have eq302068 : x = (M.op x x) := by grind
  clear eq302067
  have eq302795 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq302068
       grind)
    | exact superpose eq302068 eq76
    | exact resolve eq76 eq302068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq302068
  have eq302932 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq295451 eq302795
    | exact resolve eq302795 eq295451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302795
  have eq302966 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq301470 eq302932
    | exact resolve eq302932 eq301470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301470 eq302932
  have eq302990 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq302966
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq302966
    | exact resolve eq302966 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq302966
  have eq303009 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq295451 eq302990
    | exact resolve eq302990 eq295451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295451 eq302990
  have eq303022 : False := by grind
  exact eq303022
