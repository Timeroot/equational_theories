import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then Y else if m(Y,X) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_y_x_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
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
  have eq79 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq105 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X0) X1
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq52 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq191
    | exact resolve eq191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21 eq191
    | (have j0 := eq191 X0 (M.op x y)
       grind)
    | exact resolve eq191 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op (M.op X1 (M.op X2 X2)) X0) X3 X4 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq51 (M.op X1 X0) X4 X5 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1)
       have i₂ := eq51 X1 X2 X3 X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 x (M.op X0 X0) X2
       have i₂ := eq52 x (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2 X3
       have i₂ := eq51 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2) ∨ (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) = X2 ∨ (k X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq51 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq51 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2
       grind)
    | exact resolve eq12 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq302 (M.op X0 X0) x X1
       have i₂ := eq52 x (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq302
    | exact resolve eq302 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq302
  have eq712 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (σ X0) (σ X1)) (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (σ X0) X2 X3 (σ X0)
       have i₂ := eq79 X1 X0
       grind)
    | (have i₁ := eq51 (σ X1) X1 X2 (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq51
    | (have j1 := eq79 X1 X0
       grind)
    | exact resolve eq51 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq715 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1 x x
       have i₂ := eq51 (σ X0) x x (σ X1)
       grind)
    | exact superpose eq51 eq712
    | (have j0 := eq712 X0 X1 x x
       grind)
    | exact resolve eq712 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq712
  have eq716 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq715 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq773 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq304 X0 X1 x
       grind)
    | exact superpose eq304 eq14
    | exact resolve eq14 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq966 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X2 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq543 X2 X1 X1
       have i₂ := eq572 X0 X1
       grind)
    | (have i₁ := eq543 X2 X1 X1
       have i₂ := eq572 X1 X0
       grind)
    | exact superpose eq572 eq543
    | exact resolve eq543 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq543 X0 (M.op (M.op X1 X1) X0) X2
       have i₂ := eq543 X1 X0 X0
       grind)
    | exact superpose eq543 eq543
    | exact resolve eq543 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4502 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq716 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq716
    | (have j0 := eq716 X0 x
       grind)
    | exact resolve eq716 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4504 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq716
    | (have j0 := eq716 X0 (M.op x y)
       grind)
    | exact resolve eq716 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4505 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq716 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq716
    | exact resolve eq716 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4554 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (M.op X2 X2) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq543 X2 (σ X0) (σ X1)
       have i₂ := eq716 X1 X0
       grind)
    | exact superpose eq716 eq543
    | (have j1 := eq716 X0 X1
       grind)
    | exact resolve eq543 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4564 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4505 X0 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq4505
    | (have j0 := eq4505 X0 X1
       grind)
    | exact resolve eq4505 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4505
  have eq5858 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op (M.op x y) X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq31 eq188
    | exact resolve eq188 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq5896 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (M.op (M.op x y) X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq38 eq5858
    | (have j0 := eq5858 X0
       grind)
    | exact resolve eq5858 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858
  have eq7248 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (σ X0)) = (M.op (σ X1) (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (σ (k X0 X1)))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq538 (σ X1) (σ X0) X2 X3 X4 X5
       have i₂ := eq716 X1 X0
       grind)
    | exact superpose eq716 eq538
    | (have j1 := eq716 X0 X1
       grind)
    | exact resolve eq538 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq10126 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) = X2 ∨ (k X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq556 X0 X1 X2
       have i₂ := eq555 X0 X1 (M.op X0 X0) X1
       grind)
    | exact superpose eq555 eq556
    | (have j0 := eq556 X0 X1 X2
       grind)
    | (have r₁ := eq556 X0 X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op x x))
       have r₂ := eq555 (M.op X0 X0) (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact resolve eq556 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq10127 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X2 ∨ (M.op (M.op X0 X0) X2) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (k X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10126 X0 X1 X2
       have i₂ := eq555 X0 X1 (M.op X0 X0) X1
       grind)
    | exact superpose eq555 eq10126
    | (have j0 := eq10126 X0 X1 X2
       grind)
    | (have r₁ := eq10126 (M.op X1 X1) X1 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)) (M.op x x))
       have r₂ := eq555 X1 X1 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)) x
       grind)
    | (have r₁ := eq10126 (M.op X1 X1) (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1))) (M.op (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq555 X1 X1 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1))) (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact resolve eq10126 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10126
  have eq10128 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X0 X0) = X2 ∨ (k X2 (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10127 X0 X1 X2
       have i₂ := eq555 X0 X1 (M.op X0 X0) X1
       grind)
    | exact superpose eq555 eq10127
    | (have j0 := eq10127 X0 X1 X2
       grind)
    | (have r₁ := eq10127 (M.op X1 X1) X1 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)) (M.op x x))
       have r₂ := eq555 X1 X1 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)) x
       grind)
    | (have r₁ := eq10127 (M.op X1 X1) (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1))) (M.op (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq555 X1 X1 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1))) (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact resolve eq10127 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10127
  have eq11223 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4502 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4502
    | (have j0 := eq4502 y
       grind)
    | exact resolve eq4502 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4502
  have eq11234 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11223
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq11223
    | exact resolve eq11223 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11223
  have eq11247 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq11234
    | exact resolve eq11234 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11234
  have eq12155 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4564 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4564
    | exact resolve eq4564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4564
  have eq12420 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq47
       have i₂ := eq12155 x y
       grind)
    | exact superpose eq12155 eq47
    | (have j1 := eq12155 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq47 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq12591 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12420
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12420
    | exact resolve eq12420 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12420
  have eq12601 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq12591
    | exact resolve eq12591 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12591
  have eq12618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12601 eq11247
    | exact resolve eq11247 eq12601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11247 eq12601
  have eq12627 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12618
       have r₂ := eq28
       grind)
    | exact resolve eq12618 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12618
  have eq12653 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq12627 eq30
    | exact resolve eq30 eq12627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12627
  have eq12749 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq12653
    | exact resolve eq12653 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12653
  have eq12750 : x = y := by grind
  clear eq12749
  have eq12777 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq12750
       grind)
    | exact superpose eq12750 eq19
    | exact resolve eq19 eq12750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq12778 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq12750
       grind)
    | exact superpose eq12750 eq25
    | exact resolve eq25 eq12750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12750
  have eq12875 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12778
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12778
    | exact resolve eq12778 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq12778
  have eq12902 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12875 eq27
    | exact resolve eq27 eq12875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12875
  have eq13054 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12777
       have i₂ := eq572 X0 x
       grind)
    | (have i₁ := eq12777
       have i₂ := eq572 x X0
       grind)
    | exact superpose eq572 eq12777
    | exact resolve eq12777 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq13058 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op x y)) X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq12777
       grind)
    | exact superpose eq12777 eq14
    | exact resolve eq14 eq12777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13086 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq543 x X0 X1
       have i₂ := eq12777
       grind)
    | exact superpose eq12777 eq543
    | exact resolve eq543 eq12777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13106 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq998 X0 x X1
       have i₂ := eq12777
       grind)
    | exact superpose eq12777 eq998
    | exact resolve eq998 eq12777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998 eq12777
  have eq13232 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12902 eq13054
    | exact resolve eq13054 eq12902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12902
  have eq13292 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq543 X1 X0 X0
       have i₂ := eq13054 X0
       grind)
    | exact superpose eq13054 eq543
    | exact resolve eq543 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13312 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op X2 (M.op X3 X3)) X0))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq536 X0 X2 X3 x x
       have i₂ := eq13054 (M.op x x)
       grind)
    | exact superpose eq13054 eq536
    | exact resolve eq536 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq13314 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) = (M.op X3 (M.op (M.op x y) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq538 X3 X2 X0 X1 x x
       have i₂ := eq13054 (M.op x x)
       grind)
    | exact superpose eq13054 eq538
    | exact resolve eq538 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13316 : ∀ X1 X2 : G, (M.op (M.op x y) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq555 x x X1 X2
       have i₂ := eq13054 (M.op x x)
       grind)
    | exact superpose eq13054 eq555
    | exact resolve eq555 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq13340 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X1)) X0 X1
       have i₂ := eq13054 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq13054 eq14
    | exact resolve eq14 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13360 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq13340 X0 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq13340
    | exact resolve eq13340 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13340
  have eq13377 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq13316 X1 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq13316
    | exact resolve eq13316 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13316
  have eq13379 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) X2) = (M.op X3 (M.op (M.op x y) (M.op X2 X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq13314 X0 x X2 X3
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq13314
    | exact resolve eq13314 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13314
  have eq13381 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op X2 (M.op x y)) X0))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq13312 X0 X2 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq13312
    | exact resolve eq13312 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13312
  have eq13397 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13292 X0 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq13292
    | exact resolve eq13292 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13292
  have eq13468 : ∀ X2 X3 : G, (M.op X3 (M.op (M.op x y) (M.op X2 X3))) = (M.op (M.op (M.op x y) (M.op x y)) X2) := by
    intro X2 X3
    first
    | (have i₁ := eq13379 x X2 X3
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq13379
    | exact resolve eq13379 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13379
  have eq13509 : ∀ X2 X3 : G, (M.op (M.op x y) X2) = (M.op X3 (M.op (M.op x y) (M.op X2 X3))) := by
    intro X2 X3
    first
    | (have i₁ := eq13468 X2 X3
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq13468
    | exact resolve eq13468 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13468
  have eq13555 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq13232 eq28
    | exact resolve eq28 eq13232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13232
  have eq17123 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op X3 (M.op x y)) X0)) = (M.op X3 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq13058 eq538
    | exact resolve eq538 eq13058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13058
  have eq17158 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op X3 (M.op x y)) X0)) = (M.op X3 (M.op (M.op (M.op X4 X4) (M.op x y)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17123 X0 X1 X2 X3 X4 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq17123
    | exact resolve eq17123 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17123
  have eq17249 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op X3 (M.op x y)) X0)) = (M.op X3 (M.op (M.op (M.op x y) (M.op X4 X4)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq13360 eq17158
    | exact resolve eq17158 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17158
  have eq17307 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op X3 (M.op x y)) X0)) = (M.op X3 (M.op (M.op (M.op x y) (M.op x y)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17249 X0 X1 X2 X3 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq17249
    | exact resolve eq17249 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17249
  have eq17335 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op X3 (M.op x y)) X0)) = (M.op X3 (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17307 X0 X1 X2 X3
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq17307
    | exact resolve eq17307 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17307
  have eq17358 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X1 X1) (M.op x y)) (M.op (M.op X3 (M.op x y)) X0)) = (M.op X3 (M.op (M.op x y) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq17335 X0 X1 x X3
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq17335
    | exact resolve eq17335 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17335
  have eq17373 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) (M.op X1 X1)) (M.op (M.op X3 (M.op x y)) X0)) := by
    intro X0 X1 X3
    first
    | exact superpose eq13360 eq17358
    | exact resolve eq17358 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17358
  have eq17383 : ∀ X0 X3 : G, (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op X3 (M.op x y)) X0)) = (M.op X3 (M.op (M.op x y) X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq17373 X0 x X3
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq17373
    | exact resolve eq17373 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17373
  have eq17389 : ∀ X0 X3 : G, (M.op (M.op x y) (M.op (M.op X3 (M.op x y)) X0)) = (M.op X3 (M.op (M.op x y) X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq17383 X0 X3
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq17383
    | exact resolve eq17383 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17383
  have eq18348 : ∀ X0 : G, (σ X0) = (M.op (σ (k (M.op x y) X0)) (M.op (M.op x y) (σ (M.op x y)))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4504 eq13086
    | (have j1 := eq4504 X0
       grind)
    | exact resolve eq13086 eq4504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4504
  have eq18494 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X3 X0)) = (M.op (M.op (M.op x y) X3) (M.op (M.op (M.op X4 X4) (M.op X5 X5)) X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq13086 eq538
    | exact resolve eq538 eq13086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13086
  have eq18503 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X3 X0)) = (M.op (M.op (M.op x y) X3) (M.op (M.op (M.op X4 X4) (M.op x y)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18494 X0 X1 X2 X3 X4 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq18494
    | exact resolve eq18494 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18494
  have eq18661 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X3 X0)) = (M.op (M.op (M.op x y) X3) (M.op (M.op (M.op x y) (M.op X4 X4)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq13360 eq18503
    | exact resolve eq18503 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18503
  have eq18746 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X3 X0)) = (M.op (M.op (M.op x y) X3) (M.op (M.op (M.op x y) (M.op x y)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18661 X0 X1 X2 X3 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq18661
    | exact resolve eq18661 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18661
  have eq18801 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X3 X0)) = (M.op (M.op (M.op x y) X3) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18746 X0 X1 X2 X3
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq18746
    | exact resolve eq18746 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18746
  have eq18836 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op x y) X3) (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X1) (M.op x y)) (M.op X3 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq18801 X0 X1 x X3
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq18801
    | exact resolve eq18801 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18801
  have eq18855 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op x y) X3) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) (M.op X1 X1)) (M.op X3 X0)) := by
    intro X0 X1 X3
    first
    | exact superpose eq13360 eq18836
    | exact resolve eq18836 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18836
  have eq18869 : ∀ X0 X3 : G, (M.op (M.op (M.op x y) X3) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op X3 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq18855 X0 x X3
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq18855
    | exact resolve eq18855 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18855
  have eq18878 : ∀ X0 X3 : G, (M.op (M.op (M.op x y) X3) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op X3 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq18869 X0 X3
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq18869
    | exact resolve eq18869 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18869
  have eq20447 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq13106 X0 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X1 (M.op sF0 X0)))
       have i₂ := eq538 (M.op sF0 X0) X1 X2 X3 X4 X5
       grind)
    | exact superpose eq538 eq13106
    | exact resolve eq13106 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq20586 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op X4 X4) (M.op x y)) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20447 X0 X1 X2 X3 X4 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq20447
    | exact resolve eq20447 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20447
  have eq20639 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op x y) (M.op X4 X4)) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq13360 eq20586
    | exact resolve eq20586 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20586
  have eq20674 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op x y) (M.op x y)) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20639 X0 X1 X2 X3 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq20639
    | exact resolve eq20639 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20639
  have eq20696 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op x y) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20674 X0 X1 X2 X3
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq20674
    | exact resolve eq20674 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20674
  have eq20709 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) X2) X3) = (M.op (M.op x y) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq20696 X0 x X2 X3
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq20696
    | exact resolve eq20696 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20696
  have eq20720 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op (M.op x y) (M.op X0 X0)) X2) X3) = (M.op (M.op x y) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X2 X3
    first
    | exact superpose eq13360 eq20709
    | exact resolve eq20709 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20709
  have eq20726 : ∀ X2 X3 : G, (M.op (M.op (M.op (M.op x y) (M.op x y)) X2) X3) = (M.op (M.op x y) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X2 X3
    first
    | (have i₁ := eq20720 x X2 X3
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq20720
    | exact resolve eq20720 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20720
  have eq20730 : ∀ X2 X3 : G, (M.op (M.op (M.op x y) X2) X3) = (M.op (M.op x y) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X2 X3
    first
    | (have i₁ := eq20726 X2 X3
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq20726
    | exact resolve eq20726 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20726
  have eq21676 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op (M.op x y) (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq13509 eq13509
    | exact resolve eq13509 eq13509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13509
  have eq21900 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq13397 eq21676
    | exact resolve eq21676 eq13397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21676
  have eq24665 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq13381 eq21900
    | exact resolve eq21900 eq13381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24909 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq13397 eq24665
    | exact resolve eq24665 eq13397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24665
  have eq28077 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) X2) (M.op (M.op X0 (M.op x y)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq17389 eq13106
    | exact resolve eq13106 eq17389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13106
  have eq61929 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (M.op x y)) X0) (M.op (M.op x y) (σ (M.op x y)))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq105 eq18348
    | (have j0 := eq18348 (τ X0)
       grind)
    | exact resolve eq18348 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18348
  have eq61992 : ∀ X0 : G, (M.op (k (σ (M.op x y)) X0) (M.op (M.op x y) (σ (M.op x y)))) = X0 ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq61929 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq61929
    | (have j0 := eq61929 X0
       grind)
    | exact resolve eq61929 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61929
  have eq62023 : ∀ X0 : G, (M.op (k (σ (M.op x y)) X0) (M.op (M.op x y) (σ (M.op x y)))) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq61992 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq61992
    | (have j0 := eq61992 X0
       grind)
    | exact resolve eq61992 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61992
  have eq62088 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (σ (M.op x y)))) = (M.op (M.op (M.op x y) X0) (k (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq62023 eq21900
    | (have j1 := eq62023 X0
       grind)
    | exact resolve eq21900 eq62023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62023
  have eq62100 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op x y) X0) (k (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq13397 eq62088
    | (have j0 := eq62088 (M.op (M.op (M.op x y) X0) (k (σ (M.op x y)) X0))
       grind)
    | exact resolve eq62088 eq13397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62088
  have eq62198 : (M.op (M.op x y) (σ (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (k (σ (M.op x y)) (M.op x y)))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62100 eq17389
    | (have j1 := eq62100 (M.op x y)
       grind)
    | exact resolve eq17389 eq62100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62100
  have eq62238 : (M.op (M.op x y) (σ (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (k (σ (M.op x y)) (M.op x y)))) := by
    first
    | (have r₁ := eq62198
       have r₂ := eq13555
       grind)
    | exact resolve eq62198 eq13555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62198
  have eq62279 : (M.op (M.op x y) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq13397 eq62238
    | exact resolve eq62238 eq13397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62238
  have eq91923 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (M.op x y) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4554 X0 X1 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq4554
    | (have j0 := eq4554 X0 X1 x
       grind)
    | exact resolve eq4554 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4554
  have eq92072 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (M.op (M.op x y) (σ (τ X0)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91923 (τ X0) (τ X1)
       have i₂ := eq365 X1 X0
       grind)
    | exact superpose eq365 eq91923
    | (have j0 := eq91923 (τ X0) (τ X1)
       grind)
    | exact resolve eq91923 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq91923
  have eq92578 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (M.op (M.op x y) X0)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92072 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq92072
    | (have j0 := eq92072 X0 X1
       grind)
    | exact resolve eq92072 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92072
  have eq92782 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (k X0 X1) (M.op (M.op x y) X0)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92578 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq92578
    | (have j0 := eq92578 X0 X1
       grind)
    | exact resolve eq92578 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92578
  have eq92975 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op (M.op x y) X0)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92782 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq92782
    | (have j0 := eq92782 X0 X1
       grind)
    | exact resolve eq92782 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92782
  have eq93139 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op (k X0 X1) (M.op (M.op x y) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq92975 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq92975
    | (have j0 := eq92975 X0 X1
       grind)
    | exact resolve eq92975 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92975
  have eq93237 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op (M.op x y) X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq93139 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq93139
    | (have j0 := eq93139 X0 X1
       grind)
    | exact resolve eq93139 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93139
  have eq93467 : ∀ X0 : G, (M.op x y) = (M.op (τ (k X0 (σ (M.op x y)))) (M.op (M.op x y) (τ X0))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq379 eq93237
    | (have j0 := eq93237 (M.op x y) (M.op (τ (k X0 (σ (M.op x y)))) (M.op (M.op x y) (τ X0)))
       grind)
    | exact resolve eq93237 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq93609 : ∀ X0 X1 : G, (k (M.op x y) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq93237 eq304
    | (have j1 := eq93237 (k (M.op x y) X0) (M.op X0 (M.op X1 X1))
       grind)
    | exact resolve eq304 eq93237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq93615 : ∀ X0 X1 : G, (M.op (M.op (k (M.op x y) X0) X1) X0) = X1 ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq93237 eq773
    | (have j1 := eq93237 (M.op (M.op (k (M.op x y) X0) X1) X0) X1
       grind)
    | exact resolve eq773 eq93237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq93628 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) X1)) = (M.op (M.op (M.op x y) X0) (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq93237 eq21900
    | (have j1 := eq93237 (M.op (M.op x y) (M.op (M.op x y) X1)) (M.op (M.op (M.op x y) X0) (k X1 X0))
       grind)
    | exact resolve eq21900 eq93237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21900 eq93237
  have eq93659 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (k X1 X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq13397 eq93628
    | (have j0 := eq93628 (M.op (M.op (M.op x y) X0) (k X1 X0)) X1
       grind)
    | exact resolve eq93628 eq13397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93628
  have eq93673 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq93609 X0 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq93609
    | (have j0 := eq93609 X0 x
       grind)
    | exact resolve eq93609 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93609
  have eq95159 : ∀ X0 X1 : G, (k (M.op x y) (M.op (M.op X0 X0) X1)) = X1 ∨ (M.op x y) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq93615 eq966
    | (have j1 := eq93615 (M.op (M.op X0 X0) X1) X1
       grind)
    | exact resolve eq966 eq93615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq93615
  have eq95250 : ∀ X0 X1 : G, (k (M.op x y) (M.op (M.op x y) X1)) = X1 ∨ (M.op x y) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95159 X0 X1
       have i₂ := eq13054 X0
       grind)
    | exact superpose eq13054 eq95159
    | (have j0 := eq95159 X0 X1
       grind)
    | exact resolve eq95159 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95159
  have eq95299 : ∀ X1 : G, (k (M.op x y) (M.op (M.op x y) X1)) = X1 ∨ (M.op x y) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have i₁ := eq95250 x X1
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq95250
    | (have j0 := eq95250 x X1
       grind)
    | exact resolve eq95250 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95250
  have eq97724 : ∀ X0 : G, (M.op (M.op x y) (k X0 (M.op x y))) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq93659 sF0 x
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq93659
    | (have j0 := eq93659 (M.op (M.op x y) (k X0 (M.op x y))) X0
       grind)
    | exact resolve eq93659 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97870 : ∀ X0 X1 : G, (M.op (M.op (k X0 (M.op x y)) X1) X0) = X1 ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq93659 eq543
    | (have j1 := eq93659 (M.op (M.op (k X0 (M.op x y)) X1) X0) X1
       grind)
    | exact resolve eq543 eq93659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq97876 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) (k X0 (M.op x y)))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq93659 eq17389
    | (have j1 := eq93659 (M.op (M.op x y) X0) (M.op (M.op x y) (M.op (M.op x y) (k X0 (M.op x y))))
       grind)
    | exact resolve eq17389 eq93659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93659
  have eq97949 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq13397 eq97876
    | (have j0 := eq97876 X0
       grind)
    | exact resolve eq97876 eq13397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97876
  have eq98244 : ∀ X0 : G, (k (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq97724 eq95299
    | (have j1 := eq97724 X0
       grind)
    | exact resolve eq95299 eq97724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95299 eq97724
  have eq98264 : ∀ X0 : G, (k (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have j0 := eq98244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98244
  have eq98687 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (M.op (M.op x y) X0)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq5896 X0
       have i₂ := eq13054 X0
       grind)
    | exact superpose eq13054 eq5896
    | (have j0 := eq5896 X0
       grind)
    | exact resolve eq5896 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5896
  have eq100308 : ∀ X0 : G, (τ (k (M.op x y) (σ X0))) = (k X0 (τ (M.op x y))) ∨ (σ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq98264 eq287
    | (have j1 := eq98264 (σ X0)
       grind)
    | exact resolve eq287 eq98264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq100325 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq98264 eq35
    | (have j1 := eq98264 (τ X0)
       grind)
    | exact resolve eq35 eq98264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98264
  have eq100599 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq100325
    | (have j0 := eq100325 X0
       grind)
    | exact resolve eq100325 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100325
  have eq100615 : ∀ X0 : G, (k (τ (M.op x y)) X0) = (k X0 (τ (M.op x y))) ∨ (σ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq100308 x
       have i₂ := eq191 sF0 x
       grind)
    | exact superpose eq191 eq100308
    | (have j0 := eq100308 X0
       grind)
    | exact resolve eq100308 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq100308
  have eq100695 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq105 eq100599
    | (have j0 := eq100599 X0
       grind)
    | exact resolve eq100599 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100599
  have eq101095 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (k X0 (M.op x y))) ∨ (τ (σ X0)) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq100695 eq42
    | (have j1 := eq100695 (σ X0)
       grind)
    | exact resolve eq42 eq100695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101114 : ∀ X0 : G, (σ (k (σ (M.op x y)) (τ X0))) = (k X0 (σ (σ (M.op x y)))) ∨ (M.op x y) = (τ (τ X0)) := by
    intro X0
    first
    | exact superpose eq100695 eq35
    | (have j1 := eq100695 (τ X0)
       grind)
    | exact resolve eq35 eq100695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq100695
  have eq101303 : ∀ X0 : G, (k (σ (σ (M.op x y))) X0) = (k X0 (σ (σ (M.op x y)))) ∨ (M.op x y) = (τ (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq101114 X0
       have i₂ := eq39 X0 sF1
       grind)
    | exact superpose eq39 eq101114
    | (have j0 := eq101114 X0
       grind)
    | exact resolve eq101114 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq101114
  have eq101322 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (k X0 (M.op x y))) ∨ (τ (σ X0)) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38 eq101095
    | (have j0 := eq101095 X0
       grind)
    | exact resolve eq101095 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101095
  have eq101389 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (k X0 (M.op x y))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq101322 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq101322
    | (have j0 := eq101322 X0
       grind)
    | exact resolve eq101322 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101322
  have eq102509 : ∀ X0 X1 : G, (k X0 (M.op x y)) ≠ (M.op (M.op (k X0 (M.op x y)) (k X0 (M.op x y))) (M.op X1 X1)) ∨ (M.op (k X0 (M.op x y)) (k X0 (M.op x y))) = X0 ∨ (k X0 (M.op (k X0 (M.op x y)) (k X0 (M.op x y)))) = X0 ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq97870 eq10128
    | (have j0 := eq10128 (k X0 (M.op x y)) X1 X0
       have j1 := eq97870 X0 X1
       grind)
    | exact resolve eq10128 eq97870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10128 eq97870
  have eq102632 : ∀ X0 : G, (k X0 (M.op x y)) ≠ (M.op (M.op (k X0 (M.op x y)) (k X0 (M.op x y))) (M.op x y)) ∨ (M.op (k X0 (M.op x y)) (k X0 (M.op x y))) = X0 ∨ (k X0 (M.op (k X0 (M.op x y)) (k X0 (M.op x y)))) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq102509 X0 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq102509
    | (have j0 := eq102509 X0 x
       grind)
    | exact resolve eq102509 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102509
  have eq102678 : ∀ X0 : G, (k X0 (M.op x y)) ≠ (M.op (M.op x y) (M.op (k X0 (M.op x y)) (k X0 (M.op x y)))) ∨ (M.op (k X0 (M.op x y)) (k X0 (M.op x y))) = X0 ∨ (k X0 (M.op (k X0 (M.op x y)) (k X0 (M.op x y)))) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq13360 eq102632
    | (have j0 := eq102632 X0
       grind)
    | exact resolve eq102632 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102632
  have eq102705 : ∀ X0 : G, (k X0 (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op (k X0 (M.op x y)) (k X0 (M.op x y))) = X0 ∨ (k X0 (M.op (k X0 (M.op x y)) (k X0 (M.op x y)))) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq102678 X0
       have i₂ := eq13054 (k X0 sF0)
       grind)
    | exact superpose eq13054 eq102678
    | (have j0 := eq102678 X0
       grind)
    | exact resolve eq102678 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102678
  have eq102720 : ∀ X0 : G, (M.op x y) ≠ (k X0 (M.op x y)) ∨ (M.op (k X0 (M.op x y)) (k X0 (M.op x y))) = X0 ∨ (k X0 (M.op (k X0 (M.op x y)) (k X0 (M.op x y)))) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq102705 X0
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq102705
    | (have j0 := eq102705 X0
       grind)
    | exact resolve eq102705 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102705
  have eq102732 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op x y) ≠ (k X0 (M.op x y)) ∨ (k X0 (M.op (k X0 (M.op x y)) (k X0 (M.op x y)))) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq102720 X0
       have i₂ := eq13054 (k X0 sF0)
       grind)
    | exact superpose eq13054 eq102720
    | (have j0 := eq102720 X0
       grind)
    | exact resolve eq102720 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102720
  have eq102733 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op x y) ≠ (k X0 (M.op x y)) ∨ (k X0 (M.op (k X0 (M.op x y)) (k X0 (M.op x y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq102732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102732
  have eq102739 : ∀ X0 : G, (M.op x y) ≠ (k X0 (M.op x y)) ∨ (M.op x y) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq102733 X0
       have i₂ := eq13054 (k X0 sF0)
       grind)
    | exact superpose eq13054 eq102733
    | (have j0 := eq102733 X0
       grind)
    | exact resolve eq102733 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102733
  have eq105596 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (M.op X0 (M.op x y))) ∨ (M.op x y) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq101389 X0
       have i₂ := eq12155 X0 sF0
       grind)
    | exact superpose eq12155 eq101389
    | (have j0 := eq101389 X0
       have j1 := eq12155 (σ (k (M.op x y) X0)) (σ (M.op X0 (M.op x y)))
       grind)
    | exact resolve eq101389 eq12155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12155 eq101389
  have eq105870 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (M.op X0 (M.op x y))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have j0 := eq105596 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105596
  have eq110812 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) X0) ∨ (M.op x y) = X0 ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq97949 eq102739
    | (have j0 := eq102739 X0
       have j1 := eq97949 X0
       grind)
    | (have r₁ := eq102739 X0
       have r₂ := eq97949 (k X0 (M.op x y))
       grind)
    | exact resolve eq102739 eq97949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97949 eq102739
  have eq110836 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) X0) ∨ (M.op x y) = X0 ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq110812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110812
  have eq175594 : ∀ X0 : G, (σ (k X0 (σ (M.op x y)))) = (k (σ (σ (M.op x y))) (σ X0)) ∨ (M.op x y) = (τ (τ (σ X0))) := by
    intro X0
    first
    | exact superpose eq101303 eq10
    | (have j1 := eq101303 (σ X0)
       grind)
    | exact resolve eq10 eq101303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101303
  have eq175793 : ∀ X0 : G, (σ (k X0 (σ (M.op x y)))) = (σ (k (σ (M.op x y)) X0)) ∨ (M.op x y) = (τ (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq175594 x
       have i₂ := eq10 sF1 x
       grind)
    | exact superpose eq10 eq175594
    | (have j0 := eq175594 X0
       grind)
    | exact resolve eq175594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175594
  have eq175951 : ∀ X0 : G, (σ (k X0 (σ (M.op x y)))) = (σ (k (σ (M.op x y)) X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq175793 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq175793
    | (have j0 := eq175793 X0
       grind)
    | exact resolve eq175793 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175793
  have eq176186 : ∀ X0 : G, (σ (σ (k X0 (M.op x y)))) = (σ (k (σ (M.op x y)) (σ X0))) ∨ (τ (σ X0)) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq42 eq175951
    | (have j0 := eq175951 (σ X0)
       grind)
    | exact resolve eq175951 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq175951
  have eq176638 : ∀ X0 : G, (σ (σ (k X0 (M.op x y)))) = (σ (σ (k (M.op x y) X0))) ∨ (τ (σ X0)) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38 eq176186
    | (have j0 := eq176186 X0
       grind)
    | exact resolve eq176186 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq176186
  have eq176673 : ∀ X0 : G, (σ (σ (k X0 (M.op x y)))) = (σ (σ (k (M.op x y) X0))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq176638 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq176638
    | (have j0 := eq176638 X0
       grind)
    | exact resolve eq176638 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176638
  have eq194455 : ∀ X0 : G, (σ (σ (k X0 (M.op x y)))) = (σ (σ (M.op X0 (M.op x y)))) ∨ (M.op x y) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq105870 eq176673
    | (have j0 := eq176673 X0
       have j1 := eq105870 X0
       grind)
    | exact resolve eq176673 eq105870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105870 eq176673
  have eq194692 : ∀ X0 : G, (σ (σ (k X0 (M.op x y)))) = (σ (σ (M.op X0 (M.op x y)))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have j0 := eq194455 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194455
  have eq200273 : (σ (σ (k (M.op x y) (τ (M.op x y))))) = (σ (σ (M.op (τ (M.op x y)) (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq100615 eq194692
    | (have j0 := eq194692 (τ (M.op x y))
       have j1 := eq100615 (M.op x y)
       grind)
    | exact resolve eq194692 eq100615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100615 eq194692
  have eq200561 : (σ (σ (k (M.op x y) (τ (M.op x y))))) = (σ (σ (M.op (M.op x y) (τ (M.op x y))))) ∨ (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq13360 eq200273
    | exact resolve eq200273 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200273
  have eq200592 : (σ (k (σ (M.op x y)) (M.op x y))) = (σ (σ (M.op (M.op x y) (τ (M.op x y))))) ∨ (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq105 eq200561
    | exact resolve eq200561 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq200561
  have eq200609 : (σ (M.op (M.op x y) (σ (M.op x y)))) = (σ (σ (M.op (M.op x y) (τ (M.op x y))))) ∨ (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62279 eq200592
    | exact resolve eq200592 eq62279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62279 eq200592
  have eq200616 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op (M.op x y) (σ (M.op x y)))) = (σ (σ (M.op (M.op x y) (τ (M.op x y))))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq21 eq200609
    | exact resolve eq200609 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200609
  have eq200621 : (σ (M.op (M.op x y) (σ (M.op x y)))) = (σ (σ (M.op (M.op x y) (τ (M.op x y))))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | (have r₁ := eq200616
       have r₂ := eq13555
       grind)
    | exact resolve eq200616 eq13555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200616
  have eq205860 : (M.op x y) = (M.op (τ (M.op (σ (M.op x y)) (M.op x y))) (M.op (M.op x y) (τ (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq93673 eq93467
    | (have j0 := eq93467 (M.op x y)
       have j1 := eq93673 (M.op (τ (M.op (σ (M.op x y)) (M.op x y))) (M.op (M.op x y) (τ (M.op x y))))
       grind)
    | exact resolve eq93467 eq93673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93467 eq93673
  have eq206084 : (M.op x y) = (M.op (τ (M.op (σ (M.op x y)) (M.op x y))) (M.op (M.op x y) (τ (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | (have r₁ := eq205860
       have r₂ := eq13555
       grind)
    | exact resolve eq205860 eq13555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205860
  have eq206152 : (M.op x y) = (M.op (τ (M.op (M.op x y) (σ (M.op x y)))) (M.op (M.op x y) (τ (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq13360 eq206084
    | exact resolve eq206084 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206084
  have eq236713 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op x y)) X2)) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op (M.op x y) X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq13381 eq28077
    | exact resolve eq28077 eq13381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13381 eq28077
  have eq237227 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op x y)) X2)) = (M.op X0 (M.op (M.op x y) (M.op X1 (M.op (M.op x y) X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq17389 eq236713
    | exact resolve eq236713 eq17389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17389 eq236713
  have eq237589 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op x y)) X2)) = (M.op X0 (M.op (M.op (M.op x y) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq20730 eq237227
    | exact resolve eq237227 eq20730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20730 eq237227
  have eq315663 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (σ X0)) = (M.op (σ X1) (M.op (M.op (M.op X4 X4) (M.op x y)) (σ (k X0 X1)))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7248 X0 X1 X2 X3 X4 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq7248
    | (have j0 := eq7248 X0 X1 X2 X3 X4 x
       grind)
    | exact resolve eq7248 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7248
  have eq315664 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (σ X0)) = (M.op (σ X1) (M.op (M.op (M.op x y) (M.op X4 X4)) (σ (k X0 X1)))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq237589 eq315663
    | (have j0 := eq315663 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq315663 eq237589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237589 eq315663
  have eq315665 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (σ X0)) = (M.op (σ X1) (M.op (M.op (M.op x y) (M.op x y)) (σ (k X0 X1)))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq315664 X0 X1 X2 X3 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq315664
    | (have j0 := eq315664 X0 X1 X2 X3 x
       grind)
    | exact resolve eq315664 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315664
  have eq315666 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (σ X0)) = (M.op (σ X1) (M.op (M.op x y) (σ (k X0 X1)))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq315665 X0 X1 X2 X3
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq315665
    | (have j0 := eq315665 X0 X1 X2 X3
       grind)
    | exact resolve eq315665 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315665
  have eq315667 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (M.op x y) (σ (k X0 X1)))) = (M.op (M.op (M.op X2 X2) (M.op x y)) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq315666 X0 X1 X2 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq315666
    | (have j0 := eq315666 X0 X1 X2 x
       grind)
    | exact resolve eq315666 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315666
  have eq315668 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (M.op x y) (σ (k X0 X1)))) = (M.op (M.op (M.op x y) (M.op X2 X2)) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq24909 eq315667
    | (have j0 := eq315667 X0 X1 X2
       grind)
    | exact resolve eq315667 eq24909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24909 eq315667
  have eq315669 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (M.op x y) (σ (k X0 X1)))) = (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq315668 X0 X1 x
       have i₂ := eq13054 x
       grind)
    | exact superpose eq13054 eq315668
    | (have j0 := eq315668 X0 X1 x
       grind)
    | exact resolve eq315668 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315668
  have eq315670 : ∀ X0 X1 : G, (M.op (M.op x y) (σ X0)) = (M.op (σ X1) (M.op (M.op x y) (σ (k X0 X1)))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq315669 X0 X1
       have i₂ := eq13054 sF0
       grind)
    | exact superpose eq13054 eq315669
    | (have j0 := eq315669 X0 X1
       grind)
    | exact resolve eq315669 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13054 eq315669
  have eq316523 : ∀ X0 : G, (M.op (M.op x y) (σ (M.op x y))) = (M.op (σ X0) (M.op (M.op x y) (σ (M.op (M.op x y) X0)))) ∨ (σ X0) = (σ (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq98687 eq315670
    | (have j0 := eq315670 X0 (M.op x y)
       have j1 := eq98687 X0
       grind)
    | exact resolve eq315670 eq98687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98687 eq315670
  have eq316633 : ∀ X0 : G, (M.op (M.op x y) (σ (M.op x y))) = (M.op (σ X0) (M.op (M.op x y) (σ (M.op (M.op x y) X0)))) ∨ (σ X0) = (σ (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq316523
    | (have j0 := eq316523 X0
       grind)
    | exact resolve eq316523 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316523
  have eq316970 : ∀ X0 : G, (M.op (M.op x y) (σ (M.op x y))) = (M.op (σ X0) (M.op (M.op x y) (σ (M.op (M.op x y) X0)))) ∨ (σ X0) = (σ (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq316633
    | (have j0 := eq316633 X0
       grind)
    | exact resolve eq316633 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316633
  have eq367627 : (σ (M.op (M.op x y) (τ (M.op x y)))) = (τ (σ (M.op (M.op x y) (σ (M.op x y))))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq200621 eq16
    | exact resolve eq16 eq200621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200621
  have eq367893 : (M.op (M.op x y) (σ (M.op x y))) = (σ (M.op (M.op x y) (τ (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq367627
       have i₂ := eq16 (M.op sF0 sF1)
       grind)
    | exact superpose eq16 eq367627
    | exact resolve eq367627 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367627
  have eq1620869 : (M.op (M.op x y) (σ (M.op x y))) = (M.op (M.op (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (σ (M.op (M.op x y) (M.op (M.op x y) (τ (M.op x y))))))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op (M.op x y) (τ (M.op x y))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq367893 eq316970
    | (have j0 := eq316970 (M.op (M.op x y) (τ (M.op x y)))
       grind)
    | exact resolve eq316970 eq367893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316970 eq367893
  have eq1622494 : (M.op (M.op x y) (σ (M.op x y))) = (M.op (M.op x y) (M.op (σ (M.op x y)) (σ (M.op (M.op x y) (M.op (M.op x y) (τ (M.op x y))))))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op (M.op x y) (τ (M.op x y))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq18878 eq1620869
    | exact resolve eq1620869 eq18878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18878 eq1620869
  have eq1622683 : (M.op (M.op x y) (σ (M.op x y))) = (M.op (M.op x y) (M.op (σ (M.op x y)) (σ (τ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op (M.op x y) (τ (M.op x y))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq13397 eq1622494
    | exact resolve eq1622494 eq13397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622494
  have eq1622801 : (M.op (M.op x y) (σ (M.op x y))) = (M.op (M.op x y) (M.op (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op (M.op x y) (τ (M.op x y))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq1622683
       have i₂ := eq15 sF0
       grind)
    | exact superpose eq15 eq1622683
    | exact resolve eq1622683 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622683
  have eq1622905 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op (M.op x y) (τ (M.op x y))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq1622801
       have i₂ := eq13377 (M.op sF0 (M.op sF1 sF0))
       grind)
    | exact superpose eq13377 eq1622801
    | exact resolve eq1622801 eq13377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13377 eq1622801
  have eq1622906 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op (M.op x y) (τ (M.op x y))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by grind
  clear eq1622905
  have eq1622990 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (τ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq13360 eq1622906
    | exact resolve eq1622906 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13360 eq1622906
  have eq1623055 : (M.op x y) = (τ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq13397 eq1622990
    | exact resolve eq1622990 eq13397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622990
  have eq1623056 : (M.op x y) = (M.op (M.op x y) (τ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by grind
  clear eq1623055
  have eq1623359 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq1623056 eq110836
    | (have j0 := eq110836 (τ (M.op x y))
       grind)
    | (have r₁ := eq110836 (τ (M.op x y))
       have r₂ := eq1623056
       grind)
    | exact resolve eq110836 eq1623056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110836 eq1623056
  have eq1623769 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (τ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) := by grind
  clear eq1623359
  have eq1623770 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by grind
  clear eq1623769
  have eq1624552 : (M.op x y) = (M.op (τ (σ (M.op x y))) (M.op (M.op x y) (τ (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq1623770 eq206152
    | exact resolve eq206152 eq1623770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206152 eq1623770
  have eq1624881 : (M.op x y) = (M.op (τ (σ (M.op x y))) (M.op (M.op x y) (τ (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) := by grind
  clear eq1624552
  have eq1625074 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (τ (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq31 eq1624881
    | exact resolve eq1624881 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1624881
  have eq1625243 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq13397 eq1625074
    | exact resolve eq1625074 eq13397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13397 eq1625074
  have eq1625244 : (M.op x y) = (τ (M.op x y)) := by grind
  clear eq1625243
  have eq1625313 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1625244 eq15
    | exact resolve eq15 eq1625244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625244
  have eq1625957 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq1625313
    | exact resolve eq1625313 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1625313
  have eq1625980 : False := by grind
  exact eq1625980

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_y_pxx_y_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op (M.op (M.op X0 X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X0 X0) X1) X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X0 X0) X1) X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq62 (τ X0)
       grind)
    | exact superpose eq62 eq31
    | exact resolve eq31 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq67
    | exact resolve eq67 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq533 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq510
    | (have j0 := eq510 X0 X1
       grind)
    | exact resolve eq510 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq645 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq533 x y
       grind)
    | exact superpose eq533 eq16
    | (have j1 := eq533 x y
       grind)
    | exact resolve eq16 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq533 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq3657 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq507 X0 X1
       grind)
    | exact superpose eq507 eq13
    | (have j0 := eq13 X1 (τ X0)
       have j1 := eq507 X0 X1
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq507 X0 X1
       grind)
    | exact resolve eq13 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3663 : ∀ X0 X1 : G, (τ X0) ≠ (M.op X1 X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq507 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq3664 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3657 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3657
  have eq3670 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3664 X0 X1
       have j1 := eq3663 X0 X1
       grind)
    | (have r₁ := eq3664 X0 X1
       have r₂ := eq3663 X0 X1
       grind)
    | exact resolve eq3664 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3664
  have eq3814 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3663 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3663
    | (have r₁ := eq3663 (σ (M.op X1 X1)) X1
       have r₂ := eq10 (M.op X1 X1)
       grind)
    | exact resolve eq3663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663
  have eq3831 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3814 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3814
    | (have j0 := eq3814 X0 X1
       grind)
    | exact resolve eq3814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814
  have eq3835 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq3831 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831
  have eq3841 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 ∨ (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq3835 X0
       grind)
    | exact superpose eq3835 eq9
    | (have j1 := eq3835 X0
       grind)
    | exact resolve eq9 eq3835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3852 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq3835 X0
       grind)
    | exact superpose eq3835 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq3835 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq3835 X0
       grind)
    | exact resolve eq12 eq3835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3835
  have eq3857 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq3852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3852
  have eq3964 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq3841 X0
       grind)
    | exact superpose eq3841 eq9
    | (have j1 := eq3841 X0
       grind)
    | exact resolve eq9 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3841
  have eq4008 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (τ (σ (M.op (M.op X0 X0) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq3964 X0
       grind)
    | exact superpose eq3964 eq10
    | (have j1 := eq3964 X0
       grind)
    | exact resolve eq10 eq3964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3964
  have eq4058 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4008 X0
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq4008
    | (have j0 := eq4008 X0
       grind)
    | exact resolve eq4008 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4008
  have eq4097 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq4058 (σ X0)
       grind)
    | exact superpose eq4058 eq28
    | (have j1 := eq4058 (σ X0)
       grind)
    | exact resolve eq28 eq4058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4058
  have eq4144 : ∀ X0 : G, (k X0 (τ (σ (M.op X0 X0)))) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4097 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq4097
    | (have j0 := eq4097 X0
       grind)
    | exact resolve eq4097 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4097
  have eq4170 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4144 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4144
    | (have j0 := eq4144 X0
       grind)
    | exact resolve eq4144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144
  have eq4194 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4170 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq4170
    | (have j0 := eq4170 X0
       grind)
    | exact resolve eq4170 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4170
  have eq4450 : ∀ X0 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq4194 X0
       grind)
    | exact superpose eq4194 eq10
    | (have j1 := eq4194 X0
       grind)
    | exact resolve eq10 eq4194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4194
  have eq4502 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4450 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4450
    | (have j0 := eq4450 X0
       grind)
    | exact resolve eq4450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4450
  have eq4672 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ (M.op X0 X0))) = (τ (M.op (σ (σ (M.op X0 X0))) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq4502 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq4502
    | exact resolve eq4502 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4675 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq4502 X0
       grind)
    | exact superpose eq4502 eq9
    | (have j1 := eq4502 X0
       grind)
    | exact resolve eq9 eq4502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4677 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X0 X1) X1)) = X0 ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq4502 X0
       grind)
    | exact superpose eq4502 eq61
    | (have j1 := eq4502 X0
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq4502 X0
       grind)
    | exact resolve eq61 eq4502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq4502
  have eq4728 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) X1)) = X0 ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4677 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4677
  have eq4753 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 (M.op X0 X0))) = (τ (M.op (σ (σ (M.op X0 X0))) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq4672 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq4672
    | (have j0 := eq4672 X0
       grind)
    | exact resolve eq4672 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4672
  have eq5451 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (k (τ X0) (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq3857 (τ X0)
       grind)
    | exact superpose eq3857 eq17
    | (have j1 := eq3857 (τ X0)
       grind)
    | exact resolve eq17 eq3857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3857
  have eq5493 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (σ (k (τ X0) (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5451 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq5451
    | (have j0 := eq5451 X0
       grind)
    | exact resolve eq5451 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5451
  have eq5521 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (σ (k (τ X0) (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5493 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq5493
    | (have j0 := eq5493 X0
       grind)
    | exact resolve eq5493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5493
  have eq5547 : ∀ X0 : G, (σ (k (τ X0) (τ (M.op X0 X0)))) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5521 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq5521
    | (have j0 := eq5521 X0
       grind)
    | exact resolve eq5521 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5521
  have eq5572 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (k (σ (τ X0)) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5547 X0
       have i₂ := eq18 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq18 eq5547
    | (have j0 := eq5547 X0
       grind)
    | exact resolve eq5547 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5547
  have eq5596 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5572 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5572
    | (have j0 := eq5572 X0
       grind)
    | exact resolve eq5572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5572
  have eq7931 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ (M.op X0 X0))) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq5596 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq5596
    | exact resolve eq5596 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5596
  have eq8021 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) ∨ (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ (M.op X0 X0))) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq7931 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq7931
    | (have j0 := eq7931 X0
       grind)
    | exact resolve eq7931 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7931
  have eq8057 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ (M.op X0 X0))) X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8021 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8021
    | (have j0 := eq8021 X0
       grind)
    | exact resolve eq8021 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8021
  have eq8086 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8057 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq8057
    | (have j0 := eq8057 X0
       grind)
    | exact resolve eq8057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8057
  have eq8113 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8086 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq8086
    | (have j0 := eq8086 X0
       grind)
    | exact resolve eq8086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8086
  have eq10198 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq665 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq665
    | (have j0 := eq665 (τ X1) (τ X0)
       grind)
    | exact resolve eq665 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10262 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10198 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq10198
    | (have j0 := eq10198 X0 X1
       grind)
    | exact resolve eq10198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10198
  have eq10290 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10262 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq10262
    | (have j0 := eq10262 X0 X1
       grind)
    | exact resolve eq10262 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10262
  have eq10314 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10290 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10290
    | (have j0 := eq10290 X0 X1
       grind)
    | exact resolve eq10290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10290
  have eq10337 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10314 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq10314
    | (have j0 := eq10314 X0 X1
       grind)
    | exact resolve eq10314 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10314
  have eq10359 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X0 X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10337 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq10337
    | (have j0 := eq10337 X0 X1
       grind)
    | exact resolve eq10337 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10337
  have eq10380 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10359 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq10359
    | (have j0 := eq10359 X0 X1
       grind)
    | exact resolve eq10359 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10359
  have eq10389 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10380 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10380
    | (have j0 := eq10380 X0 X1
       grind)
    | exact resolve eq10380 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10380
  have eq10398 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10389 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10389
    | (have j0 := eq10389 X0 X1
       grind)
    | exact resolve eq10389 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10389
  have eq14793 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq8113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8113
  have eq14880 : ∀ X0 : G, (σ (τ (M.op X0 X0))) ≠ (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (σ (τ (M.op X0 X0))) = (σ (k (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq14793 (τ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq14793
    | exact resolve eq14793 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14793
  have eq14890 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (σ (τ (M.op X0 X0))) = (σ (k (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq14880 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq14880
    | (have j0 := eq14880 X0
       grind)
    | exact resolve eq14880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14880
  have eq14900 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = (k (σ (τ X0)) (M.op X0 X0)) ∨ (M.op X0 X0) ≠ (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14890 X0
       have i₂ := eq18 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq18 eq14890
    | (have j0 := eq14890 X0
       grind)
    | exact resolve eq14890 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14890
  have eq14906 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) ≠ (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14900 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14900
    | (have j0 := eq14900 X0
       grind)
    | exact resolve eq14900 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14900
  have eq14908 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14906 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq14906
    | (have j0 := eq14906 X0
       grind)
    | exact resolve eq14906 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14906
  have eq15716 : ∀ X0 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (σ (k X0 (M.op X0 X0))) = (τ (M.op (σ (σ (M.op X0 X0))) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq4753 X0
       grind)
    | exact superpose eq4753 eq10
    | (have j1 := eq4753 X0
       grind)
    | exact resolve eq10 eq4753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4753
  have eq15781 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (τ (M.op (σ (σ (M.op X0 X0))) (σ (σ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15716 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15716
    | (have j0 := eq15716 X0
       grind)
    | exact resolve eq15716 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15716
  have eq15813 : ∀ X0 : G, (σ (k (τ X0) (τ (M.op X0 X0)))) = (τ (M.op (σ (σ (τ (M.op X0 X0)))) (σ (σ (τ X0))))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15781 (τ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq15781
    | exact resolve eq15781 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15781
  have eq15988 : ∀ X0 : G, (σ (k (τ X0) (τ (M.op X0 X0)))) = (τ (M.op (σ (σ (τ (M.op X0 X0)))) (σ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15813 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15813
    | (have j0 := eq15813 X0
       grind)
    | exact resolve eq15813 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15813
  have eq15998 : ∀ X0 : G, (σ (k (τ X0) (τ (M.op X0 X0)))) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15988 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq15988
    | (have j0 := eq15988 X0
       grind)
    | exact resolve eq15988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15988
  have eq16002 : ∀ X0 : G, (k (σ (τ X0)) (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15998 X0
       have i₂ := eq18 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq18 eq15998
    | (have j0 := eq15998 X0
       grind)
    | exact resolve eq15998 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15998
  have eq16004 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16002 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16002
    | (have j0 := eq16002 X0
       grind)
    | exact resolve eq16002 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16002
  have eq16026 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14908 X0
       have i₂ := eq16004 X0
       grind)
    | exact superpose eq16004 eq14908
    | (have j0 := eq14908 X0
       have j1 := eq16004 X0
       grind)
    | exact resolve eq14908 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14908 eq16004
  have eq16184 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16026 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq16026
    | (have j0 := eq16026 X0
       grind)
    | exact resolve eq16026 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16026
  have eq16190 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq16184 X0
       grind)
    | (have r₁ := eq16184 X0
       have r₂ := eq11 (M.op X0 X0)
       grind)
    | exact resolve eq16184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16184
  have eq17252 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16190 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq16190
    | (have j1 := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq16190 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17286 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op X0 X0)
       have i₂ := eq16190 X0
       grind)
    | exact superpose eq16190 eq14
    | (have j0 := eq14 X0 (M.op X0 X0)
       have j1 := eq16190 X0
       grind)
    | exact resolve eq14 eq16190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16190
  have eq17321 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq17286 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17286
  have eq17329 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq17252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17252
  have eq17967 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4728 X0 X0
       have i₂ := eq17321 X0
       grind)
    | exact superpose eq17321 eq4728
    | (have j0 := eq4728 X0 x
       have j1 := eq17321 X0
       grind)
    | exact resolve eq4728 eq17321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4728
  have eq17968 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4675 X0 X0
       have i₂ := eq17321 X0
       grind)
    | exact superpose eq17321 eq4675
    | (have j0 := eq4675 X0 x
       have j1 := eq17321 X0
       grind)
    | exact resolve eq4675 eq17321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675 eq17321
  have eq17996 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq17968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17968
  have eq17997 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq17967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17967
  have eq18273 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) ∨ (k (τ X0) (τ (M.op X0 X0))) = (τ (M.op (σ (τ (M.op X0 X0))) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17997 (τ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq17997
    | exact resolve eq17997 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17997
  have eq18388 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (k (τ X0) (τ (M.op X0 X0))) = (τ (M.op (σ (τ (M.op X0 X0))) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18273 X0
       have i₂ := eq31 (M.op X0 X0) X0
       grind)
    | exact superpose eq31 eq18273
    | (have j0 := eq18273 X0
       grind)
    | exact resolve eq18273 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18273
  have eq18423 : ∀ X0 : G, (k (τ X0) (τ (M.op X0 X0))) = (τ (M.op (σ (τ (M.op X0 X0))) X0)) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18388 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18388
    | (have j0 := eq18388 X0
       grind)
    | exact resolve eq18388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18388
  have eq18449 : ∀ X0 : G, (k (τ X0) (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X0) X0)) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18423 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq18423
    | (have j0 := eq18423 X0
       grind)
    | exact resolve eq18423 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18423
  have eq18474 : ∀ X0 : G, (τ (k X0 (M.op X0 X0))) = (τ (M.op (M.op X0 X0) X0)) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18449 X0
       have i₂ := eq31 (M.op X0 X0) X0
       grind)
    | exact superpose eq31 eq18449
    | (have j0 := eq18449 X0
       grind)
    | exact resolve eq18449 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18449
  have eq18830 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (τ (M.op (M.op X0 X0) X0))) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (M.op X0 X0))
       have i₂ := eq18474 X0
       grind)
    | exact superpose eq18474 eq11
    | (have j1 := eq18474 X0
       grind)
    | exact resolve eq11 eq18474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18920 : ∀ X0 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) X0)) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq18474 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18474
  have eq18976 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18830 X0
       have i₂ := eq11 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq11 eq18830
    | (have j0 := eq18830 X0
       grind)
    | exact resolve eq18830 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18830
  have eq19022 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq18920 X0
       have i₂ := eq17996 X0
       grind)
    | exact superpose eq17996 eq18920
    | (have j0 := eq18920 X0
       have j1 := eq17996 X0
       grind)
    | exact resolve eq18920 eq17996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17996
  have eq19023 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq19022 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19022
  have eq23533 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq17329 X0
       grind)
    | exact superpose eq17329 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq17329 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq17329 X0
       grind)
    | exact resolve eq12 eq17329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17329
  have eq23546 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq23533 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23533
  have eq24957 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19023 X0
       have i₂ := eq18976 X0
       grind)
    | exact superpose eq18976 eq19023
    | (have j0 := eq19023 X0
       have j1 := eq18976 X0
       grind)
    | exact resolve eq19023 eq18976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18976 eq19023
  have eq25145 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq24957 X0
       have j1 := eq18920 X0
       grind)
    | (have r₁ := eq24957 X0
       have r₂ := eq18920 X0
       grind)
    | exact resolve eq24957 eq18920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18920 eq24957
  have eq26613 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq25145 X0
       have i₂ := eq23546 X0
       grind)
    | exact superpose eq23546 eq25145
    | (have j0 := eq25145 X0
       have j1 := eq23546 X0
       grind)
    | exact resolve eq25145 eq23546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23546 eq25145
  have eq26738 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq26613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26613
  have eq26827 : ∀ X0 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (τ (M.op (σ (σ (M.op X0 X0))) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq26738 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq26738
    | exact resolve eq26738 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26738
  have eq27034 : ∀ X0 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (τ (M.op (σ (σ (M.op X0 X0))) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq26827 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq26827
    | (have j0 := eq26827 X0
       grind)
    | exact resolve eq26827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26827
  have eq27037 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (τ (M.op (σ (σ (M.op X0 X0))) (σ (σ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27034 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27034
    | (have j0 := eq27034 X0
       grind)
    | exact resolve eq27034 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27034
  have eq27661 : ∀ X0 : G, (σ (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ (σ (M.op X0 X0))) (σ (σ X0)))
       have i₂ := eq27037 X0
       grind)
    | exact superpose eq27037 eq11
    | (have j1 := eq27037 X0
       grind)
    | exact resolve eq11 eq27037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27037
  have eq29228 : ∀ X0 : G, (σ (M.op (σ (τ (M.op X0 X0))) (σ (τ X0)))) = (M.op (σ (σ (τ (M.op X0 X0)))) (σ (σ (τ X0)))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27661 (τ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq27661
    | exact resolve eq27661 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27661
  have eq29352 : ∀ X0 : G, (σ (M.op (σ (τ (M.op X0 X0))) X0)) = (M.op (σ (σ (τ (M.op X0 X0)))) (σ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29228 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29228
    | (have j0 := eq29228 X0
       grind)
    | exact resolve eq29228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29228
  have eq29368 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29352 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq29352
    | (have j0 := eq29352 X0
       grind)
    | exact resolve eq29352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29352
  have eq29388 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op (σ (τ (M.op X0 X0))) (σ (τ X0))) ∨ (τ (τ X0)) = (τ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq29368 (τ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq29368
    | exact resolve eq29368 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq29368
  have eq29523 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op (σ (τ (M.op X0 X0))) X0) ∨ (τ (τ X0)) = (τ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq29388 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29388
    | (have j0 := eq29388 X0
       grind)
    | exact resolve eq29388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29388
  have eq29534 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (M.op X0 X0))) ∨ (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq29523 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq29523
    | (have j0 := eq29523 X0
       grind)
    | exact resolve eq29523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29523
  have eq30572 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (τ (τ X0))) ∨ (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (τ (M.op X0 X0))
       have i₂ := eq29534 X0
       grind)
    | exact superpose eq29534 eq11
    | (have j1 := eq29534 X0
       grind)
    | exact resolve eq11 eq29534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29534
  have eq30786 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30572 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq30572
    | (have j0 := eq30572 X0
       grind)
    | exact resolve eq30572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30572
  have eq30897 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq30786 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30786
    | exact resolve eq30786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30786
  have eq31033 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ (M.op X0 X0))) X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq30897 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq30897
    | (have j0 := eq30897 X0
       grind)
    | exact resolve eq30897 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30897
  have eq31046 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq31033 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq31033
    | (have j0 := eq31033 X0
       grind)
    | exact resolve eq31033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31033
  have eq31052 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = X0 ∨ (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31046 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq31046
    | (have j0 := eq31046 X0
       grind)
    | exact resolve eq31046 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31046
  have eq31054 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31052 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq31052
    | (have j0 := eq31052 X0
       grind)
    | exact resolve eq31052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31052
  have eq48565 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3670 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3670
    | exact resolve eq3670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48606 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq3670 X0 X1
       grind)
    | exact superpose eq3670 eq18
    | (have j1 := eq3670 X0 X1
       grind)
    | exact resolve eq18 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670
  have eq48761 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = X0 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48606 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48606
    | (have j0 := eq48606 X0 X1
       grind)
    | exact resolve eq48606 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48606
  have eq48773 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48565 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq48565
    | (have j0 := eq48565 X0 X1
       grind)
    | exact resolve eq48565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48565
  have eq49008 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq48773 X0 X1
       grind)
    | exact superpose eq48773 eq10
    | (have j1 := eq48773 X0 X1
       grind)
    | exact resolve eq10 eq48773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48773
  have eq49102 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49008 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq49008
    | (have j0 := eq49008 X0 X1
       grind)
    | exact resolve eq49008 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49008
  have eq49269 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq49102 (σ X0) X1
       grind)
    | exact superpose eq49102 eq22
    | (have j1 := eq49102 (σ X0) X1
       grind)
    | exact resolve eq22 eq49102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49323 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq49102 X0 (σ X1)
       grind)
    | exact superpose eq49102 eq28
    | (have j1 := eq49102 X0 (σ X1)
       grind)
    | exact resolve eq28 eq49102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq49458 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49323 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq49323
    | (have j0 := eq49323 X0 X1
       grind)
    | exact resolve eq49323 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49323
  have eq49514 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48761 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48761
    | (have j0 := eq48761 (σ X0) X1
       grind)
    | exact resolve eq48761 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48761
  have eq49705 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49514 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq49514
    | (have j0 := eq49514 X0 X1
       grind)
    | exact resolve eq49514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49514
  have eq49719 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49705 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq49705
    | (have j0 := eq49705 X0 X1
       grind)
    | exact resolve eq49705 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49705
  have eq50451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq645
       have i₂ := eq49719 x y
       grind)
    | exact superpose eq49719 eq645
    | (have j1 := eq49719 x y
       grind)
    | (have r₁ := eq645
       have r₂ := eq49719 x y
       grind)
    | exact resolve eq645 eq49719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49719
  have eq50527 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq50451
  have eq50549 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq665 x y
       grind)
    | (have r₁ := eq50527
       have r₂ := eq665 x y
       grind)
    | exact resolve eq50527 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq50527
  have eq131180 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq49269 X0 X1
       grind)
    | exact superpose eq49269 eq22
    | (have j1 := eq49269 X0 X1
       grind)
    | exact resolve eq22 eq49269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49269
  have eq131457 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq131180 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq131180
    | (have j0 := eq131180 X0 X1
       grind)
    | exact resolve eq131180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131180
  have eq132188 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq131457 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq131457
    | (have j0 := eq131457 (τ X0) X1
       grind)
    | exact resolve eq131457 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131457
  have eq132493 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq132188 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq132188
    | (have j0 := eq132188 X0 X1
       grind)
    | exact resolve eq132188 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132188
  have eq132507 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq132493 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq132493
    | (have j0 := eq132493 X0 X1
       grind)
    | exact resolve eq132493 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq132493
  have eq133940 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq132507 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132507
  have eq134910 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (σ X0))
       have i₂ := eq49458 X1 X0
       grind)
    | exact superpose eq49458 eq11
    | (have j1 := eq49458 X1 X0
       grind)
    | exact resolve eq11 eq49458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49458
  have eq135100 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq134910 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq134910
    | (have j0 := eq134910 X0 X1
       grind)
    | exact resolve eq134910 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq134910
  have eq135942 : ∀ X0 X1 : G, (M.op X1 (σ X0)) ≠ X1 ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq135100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135100
  have eq138562 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50549
       grind)
    | exact superpose eq50549 eq16
    | exact resolve eq16 eq50549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138578 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq133940 (σ y) (σ x)
       have i₂ := eq50549
       grind)
    | exact superpose eq50549 eq133940
    | (have j0 := eq133940 (σ y) (σ x)
       grind)
    | exact resolve eq133940 eq50549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133940
  have eq138579 : (σ x) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq50549
  have eq138580 : (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq138578
  have eq138584 : (τ (σ x)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq138580
       have i₂ := eq22 (σ y) x
       grind)
    | exact superpose eq22 eq138580
    | exact resolve eq138580 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq138580
  have eq138600 : (k y x) = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq138584
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq138584
    | exact resolve eq138584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138584
  have eq138614 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq138600
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq138600
    | exact resolve eq138600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138600
  have eq138624 : (σ x) = (σ (M.op y y)) ∨ x = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq138614
       have i₂ := eq76 y
       grind)
    | exact superpose eq76 eq138614
    | exact resolve eq138614 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138614
  have eq138627 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq138624
       have r₂ := eq138579
       grind)
    | exact resolve eq138624 eq138579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138579 eq138624
  have eq138631 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ x = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq138627
       grind)
    | exact superpose eq138627 eq16
    | exact resolve eq16 eq138627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138636 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq90 y (σ x)
       have i₂ := eq138627
       grind)
    | exact superpose eq138627 eq90
    | (have j0 := eq90 y (σ x)
       grind)
    | (have r₁ := eq90 y (σ x)
       have r₂ := eq138627
       grind)
    | exact resolve eq90 eq138627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138627
  have eq138649 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq138636
  have eq138660 : x = (k y x) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq138649
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq138649
    | exact resolve eq138649 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138649
  have eq138702 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq138660
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq138660
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq138660 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138660
  have eq138744 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq138702
  have eq138763 : x ≠ x ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq138744
       grind)
    | exact superpose eq138744 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq138744
       grind)
    | exact resolve eq13 eq138744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138744
  have eq138777 : x = (M.op y y) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq138763
  have eq138778 : x = (k y x) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq138777
       have r₂ := eq138631
       grind)
    | exact resolve eq138777 eq138631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138631 eq138777
  have eq138790 : x ≠ x ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10398 y x
       have i₂ := eq138778
       grind)
    | exact superpose eq138778 eq10398
    | (have j0 := eq10398 y x
       grind)
    | (have r₁ := eq10398 y x
       have r₂ := eq138778
       grind)
    | exact resolve eq10398 eq138778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10398 eq138778
  have eq138813 : x ≠ x ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq138790
  have eq138814 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq138813
  have eq146501 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq138562
       have i₂ := eq138814
       grind)
    | exact superpose eq138814 eq138562
    | exact resolve eq138562 eq138814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138562 eq138814
  have eq146506 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq146501
  have eq146507 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq146506
  have eq146519 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq90 y (σ x)
       have i₂ := eq146507
       grind)
    | exact superpose eq146507 eq90
    | (have j0 := eq90 y (σ x)
       grind)
    | (have r₁ := eq90 y (σ x)
       have r₂ := eq146507
       grind)
    | exact resolve eq90 eq146507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq146507
  have eq146532 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq146519
  have eq146545 : (σ (k y x)) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq146532
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq146532
    | exact resolve eq146532 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146532
  have eq146610 : (k y x) = (τ (σ (M.op y y))) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq146545
       grind)
    | exact superpose eq146545 eq10
    | exact resolve eq10 eq146545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146545
  have eq146870 : (k y x) = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq146610
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq146610
    | exact resolve eq146610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146610
  have eq146872 : (k y x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq146870
       have r₂ := eq12 y x
       grind)
    | exact resolve eq146870 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146870
  have eq146923 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq49102 x y
       have i₂ := eq146872
       grind)
    | exact superpose eq146872 eq49102
    | (have j0 := eq49102 x y
       grind)
    | exact resolve eq49102 eq146872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49102 eq146872
  have eq146942 : x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq146923
  have eq147244 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq31054 y
       have i₂ := eq146942
       grind)
    | exact superpose eq146942 eq31054
    | exact resolve eq31054 eq146942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31054 eq146942
  have eq147396 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq147244
       have r₂ := eq16
       grind)
    | exact resolve eq147244 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147244
  have eq147412 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq147396
       grind)
    | exact superpose eq147396 eq16
    | exact resolve eq16 eq147396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147396
  have eq147417 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq147412
       have r₂ := eq76 x
       grind)
    | exact resolve eq147412 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq147412
  have eq147433 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq147417
       grind)
    | exact superpose eq147417 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq147417
       grind)
    | exact resolve eq12 eq147417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148647 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq147433 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147433
  have eq148799 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq645
       have i₂ := eq148647
       grind)
    | exact superpose eq148647 eq645
    | exact resolve eq645 eq148647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq148829 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq148799
  have eq148836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq148829
       have i₂ := eq147417
       grind)
    | exact superpose eq147417 eq148829
    | exact resolve eq148829 eq147417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148829
  have eq148840 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq148836
       have r₂ := eq16
       grind)
    | exact resolve eq148836 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148836
  have eq148853 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq148840
       grind)
    | exact superpose eq148840 eq16
    | exact resolve eq16 eq148840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148855 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq135942 y (σ x)
       have i₂ := eq148840
       grind)
    | exact superpose eq148840 eq135942
    | (have j0 := eq135942 y (σ x)
       grind)
    | (have r₁ := eq135942 y (σ x)
       have r₂ := eq148840
       grind)
    | exact resolve eq135942 eq148840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135942 eq148840
  have eq148873 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq148855
  have eq148888 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq148873
       have i₂ := eq147417
       grind)
    | exact superpose eq147417 eq148873
    | exact resolve eq148873 eq147417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147417 eq148873
  have eq148901 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq148888
       have r₂ := eq148853
       grind)
    | exact resolve eq148888 eq148853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148888
  have eq148913 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq148901
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq148901
    | exact resolve eq148901 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148901
  have eq148925 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq148913
       have i₂ := eq148647
       grind)
    | exact superpose eq148647 eq148913
    | exact resolve eq148913 eq148647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148647 eq148913
  have eq148935 : False := by grind
  exact eq148935

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pxy_pxy_pxx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
  have eq316 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq316
  have eq323 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq336 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq323 (σ X0)
       grind)
    | exact superpose eq323 eq15
    | exact resolve eq15 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq323 (τ X0)
       grind)
    | exact superpose eq323 eq32
    | exact resolve eq32 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq342
    | exact resolve eq342 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq355 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq336 X0
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq336
    | exact resolve eq336 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq336
  have eq401 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq355 X0
       grind)
    | exact superpose eq355 eq13
    | exact resolve eq13 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq407 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq402 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq402
    | exact resolve eq402 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq412 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq407
  have eq663 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq666 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq689 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 X1
       have i₂ := eq355 X0
       grind)
    | exact superpose eq355 eq666
    | (have j0 := eq666 X0 X1
       grind)
    | exact resolve eq666 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq703 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1
       have i₂ := eq355 X0
       grind)
    | exact superpose eq355 eq689
    | (have j0 := eq689 X0 X1
       grind)
    | exact resolve eq689 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq689
  have eq4149 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq703 x y
       grind)
    | exact superpose eq703 eq16
    | (have j1 := eq703 x y
       grind)
    | exact resolve eq16 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4173 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq703 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq5640 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq663
    | exact resolve eq663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq5740 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5640 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5640
    | (have j0 := eq5640 X0 X1
       grind)
    | exact resolve eq5640 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5640
  have eq17822 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4149
       have i₂ := eq5740 y x
       grind)
    | exact superpose eq5740 eq4149
    | (have j1 := eq5740 y x
       grind)
    | (have r₁ := eq4149
       have r₂ := eq5740 y x
       grind)
    | exact resolve eq4149 eq5740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149 eq5740
  have eq17823 : (M.op x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq17822
  have eq17847 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4173 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq4173
    | (have j0 := eq4173 (τ X0) (τ X1)
       grind)
    | exact resolve eq4173 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq17921 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17847 X0 X1
       have i₂ := eq349 X0
       grind)
    | exact superpose eq349 eq17847
    | (have j0 := eq17847 X0 X1
       grind)
    | exact resolve eq17847 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17847
  have eq17961 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17921 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq17921
    | (have j0 := eq17921 X0 X1
       grind)
    | exact resolve eq17921 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17921
  have eq18000 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17961 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq17961
    | (have j0 := eq17961 X0 X1
       grind)
    | exact resolve eq17961 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17961
  have eq18039 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18000 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq18000
    | (have j0 := eq18000 X0 X1
       grind)
    | exact resolve eq18000 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18000
  have eq18062 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18039 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18039
    | (have j0 := eq18039 X0 X1
       grind)
    | exact resolve eq18039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18039
  have eq18084 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18062 X0 X1
       have i₂ := eq349 X0
       grind)
    | exact superpose eq349 eq18062
    | (have j0 := eq18062 X0 X1
       grind)
    | exact resolve eq18062 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18062
  have eq18102 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18084 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq18084
    | (have j0 := eq18084 X0 X1
       grind)
    | exact resolve eq18084 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18084
  have eq18118 : ∀ X0 X1 : G, (σ (τ X1)) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18102 X0 X1
       have i₂ := eq349 X0
       grind)
    | exact superpose eq349 eq18102
    | (have j0 := eq18102 X0 X1
       grind)
    | exact resolve eq18102 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq18102
  have eq18129 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18118 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq18118
    | (have j0 := eq18118 X0 X1
       grind)
    | exact resolve eq18118 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18118
  have eq18140 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18129 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq18129
    | (have j0 := eq18129 X0 X1
       grind)
    | exact resolve eq18129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18129
  have eq54484 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq17823
       grind)
    | exact superpose eq17823 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17823
       grind)
    | exact resolve eq13 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17823
  have eq54485 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq54484
  have eq54486 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq54485
  have eq67164 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq401 x (σ y)
       have i₂ := eq54486
       grind)
    | exact superpose eq54486 eq401
    | (have j0 := eq401 x (σ y)
       grind)
    | (have r₁ := eq401 x (σ y)
       have r₂ := eq54486
       grind)
    | exact resolve eq401 eq54486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54486
  have eq67178 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq67164
  have eq67179 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq67178
  have eq67182 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq67179
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq67179
    | exact resolve eq67179 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67179
  have eq67198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq412 x
       have i₂ := eq67182
       grind)
    | exact superpose eq67182 eq412
    | exact resolve eq412 eq67182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67182
  have eq67234 : (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq67198
       have r₂ := eq16
       grind)
    | exact resolve eq67198 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67198
  have eq67239 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4173 x y
       have i₂ := eq67234
       grind)
    | exact superpose eq67234 eq4173
    | (have j0 := eq4173 x y
       grind)
    | (have r₁ := eq4173 x y
       have r₂ := eq67234
       grind)
    | exact resolve eq4173 eq67234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67234
  have eq67295 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq67239
  have eq67296 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq67295
  have eq67300 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have j1 := eq4173 x y
       grind)
    | (have r₁ := eq67296
       have r₂ := eq4173 x y
       grind)
    | exact resolve eq67296 eq4173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4173 eq67296
  have eq67303 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67300
       grind)
    | exact superpose eq67300 eq16
    | exact resolve eq16 eq67300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67304 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq401 x (σ y)
       have i₂ := eq67300
       grind)
    | exact superpose eq67300 eq401
    | (have j0 := eq401 x (σ y)
       grind)
    | (have r₁ := eq401 x (σ y)
       have r₂ := eq67300
       grind)
    | exact resolve eq401 eq67300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq67300
  have eq67318 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq67304
  have eq67319 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq67318
  have eq67322 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq67319
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq67319
    | exact resolve eq67319 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67319
  have eq67341 : (k x y) = (τ (σ (M.op x x))) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq67322
       grind)
    | exact superpose eq67322 eq10
    | exact resolve eq10 eq67322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67322
  have eq67545 : (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq67341
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq67341
    | exact resolve eq67341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67341
  have eq67595 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq18140 x y
       have i₂ := eq67545
       grind)
    | exact superpose eq67545 eq18140
    | (have j0 := eq18140 x y
       grind)
    | (have r₁ := eq18140 x y
       have r₂ := eq67545
       grind)
    | exact resolve eq18140 eq67545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18140 eq67545
  have eq67611 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq67595
  have eq67617 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq67303
       have i₂ := eq67611
       grind)
    | exact superpose eq67611 eq67303
    | exact resolve eq67303 eq67611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67303 eq67611
  have eq67625 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq67617
  have eq67626 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq67625
  have eq67635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq412 x
       have i₂ := eq67626
       grind)
    | exact superpose eq67626 eq412
    | exact resolve eq412 eq67626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67626
  have eq67671 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq67635
       have r₂ := eq16
       grind)
    | exact resolve eq67635 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67635
  have eq67689 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq67671
       grind)
    | exact superpose eq67671 eq10
    | exact resolve eq10 eq67671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67671
  have eq67890 : y = (M.op x x) := by
    first
    | (have i₁ := eq67689
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq67689
    | exact resolve eq67689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67689
  have eq67921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq412 x
       have i₂ := eq67890
       grind)
    | exact superpose eq67890 eq412
    | exact resolve eq412 eq67890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq67890
  have eq67958 : False := by grind
  exact eq67958

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_pyx_pxx_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq98 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq103 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq100
  have eq179 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq184 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq188 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq179
    | (have j0 := eq179 X0 X1
       grind)
    | exact resolve eq179 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq631 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq188 x y
       grind)
    | exact superpose eq188 eq16
    | (have j1 := eq188 x y
       grind)
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq1141 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq184 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq184
    | exact resolve eq184 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1192 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1141 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1141
    | (have j0 := eq1141 X0 X1
       grind)
    | exact resolve eq1141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq5270 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq631
       have i₂ := eq1192 x y
       grind)
    | exact superpose eq1192 eq631
    | (have j1 := eq1192 x y
       grind)
    | (have r₁ := eq631
       have r₂ := eq1192 x y
       grind)
    | (have r₁ := eq631
       have r₂ := eq1192 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq631
       have r₂ := eq1192 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq631 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq1192
  have eq5271 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq5270
  have eq5273 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5271
       grind)
    | exact superpose eq5271 eq16
    | exact resolve eq16 eq5271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq5274 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5273
       have r₂ := eq82 x
       grind)
    | exact resolve eq5273 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273
  have eq5281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq5274
       grind)
    | exact superpose eq5274 eq103
    | exact resolve eq103 eq5274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5274
  have eq5301 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq5281
       have r₂ := eq16
       grind)
    | exact resolve eq5281 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5281
  have eq5304 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5301
       grind)
    | exact superpose eq5301 eq10
    | exact resolve eq10 eq5301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5301
  have eq5359 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5304
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5304
    | exact resolve eq5304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5304
  have eq5362 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5359
       grind)
    | exact superpose eq5359 eq16
    | exact resolve eq16 eq5359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5359
  have eq5363 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq5362
       have r₂ := eq82 x
       grind)
    | exact resolve eq5362 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq5362
  have eq5373 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5363
       grind)
    | exact superpose eq5363 eq10
    | exact resolve eq10 eq5363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5363
  have eq5428 : x = (M.op y y) := by
    first
    | (have i₁ := eq5373
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5373
    | exact resolve eq5373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5373
  have eq5443 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq5428
       grind)
    | exact superpose eq5428 eq103
    | exact resolve eq103 eq5428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq5428
  have eq5462 : False := by grind
  exact eq5462

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_x_pxy_x_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq219 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq12
    | (have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq12 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq227 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq231 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq227 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq227
    | (have j0 := eq227 X0 X1
       grind)
    | exact resolve eq227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq232 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq231 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq396 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq232
    | exact resolve eq232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq416 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq426 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq396
    | (have j0 := eq396 X0 X1
       grind)
    | exact resolve eq396 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq396
  have eq760 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq426
    | exact resolve eq426 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq851 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq760 (τ X0) X1
       grind)
    | exact superpose eq760 eq18
    | (have j1 := eq760 (τ X0) X1
       grind)
    | exact resolve eq18 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq760
  have eq1123 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq851 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq851
    | exact resolve eq851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq1167 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1123 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1123
    | (have j0 := eq1123 X0 X1
       grind)
    | exact resolve eq1123 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1308 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq403
       have i₂ := eq1167 x y
       grind)
    | exact superpose eq1167 eq403
    | (have j1 := eq1167 (σ x) (σ y)
       grind)
    | (have r₁ := eq403
       have r₂ := eq1167 x y
       grind)
    | exact resolve eq403 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq1309 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1308
  have eq1367 : y ≠ y ∨ y = (k y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1309
       grind)
    | exact superpose eq1309 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1309
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1309
       grind)
    | exact resolve eq13 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1368 : y = (M.op y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1367
  have eq3968 : y ≠ (M.op x y) ∨ y = (k y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1368
       grind)
    | exact superpose eq1368 eq12
    | exact resolve eq12 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368
  have eq3969 : y ≠ (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3968
  have eq3970 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3969
       have r₂ := eq1309
       grind)
    | exact resolve eq3969 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309 eq3969
  have eq4132 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq416 x y
       have i₂ := eq3970
       grind)
    | exact superpose eq3970 eq416
    | (have j0 := eq416 x y
       grind)
    | exact resolve eq416 eq3970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq3970
  have eq4151 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4132
  have eq4152 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4151
  have eq4160 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4152
       grind)
    | exact superpose eq4152 eq16
    | exact resolve eq16 eq4152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4164 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4152
       grind)
    | exact superpose eq4152 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq4152
       grind)
    | exact resolve eq13 eq4152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4165 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq4164
  have eq4166 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq4165
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4165
    | exact resolve eq4165 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4165
  have eq6200 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq4166
       grind)
    | exact superpose eq4166 eq12
    | exact resolve eq12 eq4166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166
  have eq6204 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq6200
       have r₂ := eq4152
       grind)
    | exact resolve eq6200 eq4152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4152 eq6200
  have eq6223 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq6204
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6204
    | exact resolve eq6204 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6204
  have eq6224 : (σ y) = (σ (k y x)) := by grind
  clear eq6223
  have eq6234 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1167 x y
       have i₂ := eq6224
       grind)
    | exact superpose eq6224 eq1167
    | (have j0 := eq1167 x y
       grind)
    | exact resolve eq1167 eq6224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq6224
  have eq6323 : y = (M.op x y) := by
    first
    | (have r₁ := eq6234
       have r₂ := eq4160
       grind)
    | exact resolve eq6234 eq4160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6234
  have eq6453 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4160
       have i₂ := eq6323
       grind)
    | exact superpose eq6323 eq4160
    | exact resolve eq4160 eq6323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4160 eq6323
  have eq6456 : False := by grind
  exact eq6456

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pyx_pyx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq130 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq58 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq12
    | (have j1 := eq58 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq12 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq134 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq130 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq134
    | (have j0 := eq134 X0 X1
       grind)
    | exact resolve eq134 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq325 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq139
    | exact resolve eq139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq139 x y
       grind)
    | exact superpose eq139 eq16
    | (have j1 := eq139 x y
       grind)
    | exact resolve eq16 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq342 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq325
    | (have j0 := eq325 X0 X1
       grind)
    | exact resolve eq325 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq325
  have eq347 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq342
    | exact resolve eq342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq436 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq331
       have i₂ := eq347 x y
       grind)
    | exact superpose eq347 eq331
    | (have j1 := eq347 (σ x) (σ y)
       grind)
    | (have r₁ := eq331
       have r₂ := eq347 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq331
       have r₂ := eq347 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq331 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq347
  have eq439 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq436
  have eq486 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq439
       grind)
    | exact superpose eq439 eq10
    | exact resolve eq10 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq520 : x = y ∨ x = y := by
    first
    | (have i₁ := eq486
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq486
    | exact resolve eq486 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq521 : x = y := by grind
  clear eq520
  have eq523 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq521
       grind)
    | exact superpose eq521 eq16
    | exact resolve eq16 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq524 : False := by grind
  exact eq524

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyx_x_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq35
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq84 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq135 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq126
    | (have j0 := eq126 X0 X1
       grind)
    | exact resolve eq126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq142 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq135 X1 X0
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq135 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq135 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq135
  have eq159 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq142
    | exact resolve eq142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq142 (σ X1) X0
       grind)
    | exact superpose eq142 eq15
    | (have j1 := eq142 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq202 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq159 X0 (τ X1)
       grind)
    | exact superpose eq159 eq18
    | (have j1 := eq159 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq159
  have eq441 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq202
    | exact resolve eq202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq478 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq441
    | (have j0 := eq441 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq441 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq936 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq164 x y
       grind)
    | exact superpose eq164 eq16
    | (have j1 := eq164 x y
       grind)
    | exact resolve eq16 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq1039 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq936
       have i₂ := eq478 y x
       grind)
    | exact superpose eq478 eq936
    | (have j1 := eq478 (σ x) (σ y)
       grind)
    | (have r₁ := eq936
       have r₂ := eq478 y x
       grind)
    | (have r₁ := eq936
       have r₂ := eq478 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq936
       have r₂ := eq478 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq936 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq936
  have eq1040 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1039
  have eq1044 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1040
       grind)
    | exact superpose eq1040 eq10
    | exact resolve eq10 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1087 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1044
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1044
    | exact resolve eq1044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1088 : x = y := by grind
  clear eq1087
  have eq1179 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1088
       grind)
    | exact superpose eq1088 eq16
    | exact resolve eq16 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1180 : False := by grind
  exact eq1180

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pxy_pyx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq347 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq364 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq347 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq347
    | (have j0 := eq347 (σ X0) (σ X1)
       grind)
    | exact resolve eq347 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq722 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq364 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq364 X0 X1
       grind)
    | exact superpose eq364 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq364 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq364 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq364 X0 X1
       grind)
    | exact resolve eq13 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq726 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq722 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq731 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq726 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq726 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq726 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq741 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq731 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq731
    | (have j0 := eq731 X0 X1
       grind)
    | exact resolve eq731 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq742 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq741 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq755 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq742 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq742
    | exact resolve eq742 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq773 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq755 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq755
    | exact resolve eq755 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq785 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq773 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq773
    | exact resolve eq773 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq795 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq785 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq785
    | exact resolve eq785 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq801 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X0 X1
       have i₂ := eq795 X0 X1
       grind)
    | exact superpose eq795 eq742
    | exact resolve eq742 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq795
  have eq831 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq801 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq832 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq831 x y
       grind)
    | exact superpose eq831 eq16
    | (have r₁ := eq16
       have r₂ := eq831 x y
       grind)
    | exact resolve eq16 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq844 : False := by grind
  exact eq844
