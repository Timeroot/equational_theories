import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_y_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq393 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq38
    | exact resolve eq38 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq393 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq393
    | exact resolve eq393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq445 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq343 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq343
    | exact resolve eq343 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq343
  have eq467 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq445 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq445
    | exact resolve eq445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x x X1
       have i₂ := eq178 x x X0
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X3 ∨ (k X3 X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X2
       have i₂ := eq178 X0 X1 X2
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op (M.op X1 X1) X0)) X2
       have r₂ := eq178 X0 X1 X2
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 X2
       have i₂ := eq178 X0 X1 (σ X2)
       grind)
    | exact superpose eq178 eq467
    | exact resolve eq467 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq707 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq425 X2
       have i₂ := eq178 X0 X1 (τ X2)
       grind)
    | exact superpose eq178 eq425
    | exact resolve eq425 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq709 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 (M.op X1 X1)
       have i₂ := eq178 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq711 : ∀ X0 X2 : G, (k (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq707 X0 x X2
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq707
    | exact resolve eq707 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq712 : ∀ X0 X2 : G, (k (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq706 X0 x X2
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq706
    | exact resolve eq706 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq719 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X3 ∨ (k X3 X2) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq699 X0 x X2 X3
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq699
    | (have j0 := eq699 X0 x X2 X3
       grind)
    | (have r₁ := eq699 (M.op X0 X0) x X2 (M.op (M.op x x) (M.op X0 X0))
       have r₂ := eq709 X0 (M.op (M.op x x) (M.op X0 X0))
       grind)
    | (have r₁ := eq699 X0 x X2 (M.op (M.op X0 X0) (M.op X0 (M.op (M.op x x) X0)))
       have r₂ := eq709 X0 (M.op X0 (M.op (M.op x x) X0))
       grind)
    | exact resolve eq699 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq709
  have eq829 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ (M.op X1 X1))
       have i₂ := eq711 X1 (τ X0)
       grind)
    | exact superpose eq711 eq38
    | exact resolve eq38 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq842 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq829
    | exact resolve eq829 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq895 : (M.op y y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq897 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq698 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq698 X0 X1
       grind)
    | exact superpose eq698 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq698 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq698 X1 X1
       grind)
    | exact resolve eq12 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq927 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq914 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq2202 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 X1 (σ (M.op X1 X1))
       have i₂ := eq927 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq927 eq711
    | (have j1 := eq927 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq711 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq2203 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq842 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq927 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq927 eq842
    | (have j1 := eq927 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact resolve eq842 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq2212 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq927 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq2219 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203
  have eq2220 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2333 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq2220 (M.op X1 X1) X0
       grind)
    | exact superpose eq2220 eq16
    | exact resolve eq16 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2924 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2333 X1 (σ (M.op X1 X1))
       have i₂ := eq2219 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq2219 eq2333
    | exact resolve eq2333 eq2219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219 eq2333
  have eq4683 : ∀ X0 X1 : G, (k x (σ (M.op X1 X1))) = (τ (k (σ x) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ (M.op X1 X1))
       have i₂ := eq2924 X1 X0
       grind)
    | exact superpose eq2924 eq44
    | exact resolve eq44 eq2924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq4699 : ∀ X0 X1 : G, (k x (σ (M.op X1 X1))) = (k x (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq44 eq4683
    | exact resolve eq4683 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq4683
  have eq5848 : ∀ X0 : G, y = (M.op (M.op (M.op y x) (M.op X0 X0)) y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq895
       grind)
    | exact superpose eq895 eq16
    | exact resolve eq16 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq5851 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5848 x
       have i₂ := eq16 x y x
       grind)
    | exact superpose eq16 eq5848
    | exact resolve eq5848 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5848
  have eq9575 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (M.op X0 X0)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq897 eq16
    | exact resolve eq16 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq9578 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9575 x
       have i₂ := eq16 sF2 sF3 x
       grind)
    | exact superpose eq16 eq9575
    | exact resolve eq9575 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9575
  have eq23090 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq5851
       grind)
    | exact superpose eq5851 eq40
    | exact resolve eq40 eq5851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5851
  have eq23093 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23090
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23090
    | exact resolve eq23090 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23090
  have eq23095 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq23093
    | exact resolve eq23093 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23093
  have eq37096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23095 eq9578
    | exact resolve eq9578 eq23095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9578 eq23095
  have eq37105 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq37096
       have r₂ := eq27
       grind)
    | exact resolve eq37096 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37096
  have eq37138 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq37105 eq712
    | exact resolve eq712 eq37105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq37105
  have eq37476 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq37138
    | exact resolve eq37138 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37138
  have eq37552 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq37476 X0
       have j1 := eq719 X0 X0 x
       grind)
    | (have r₁ := eq37476 (M.op X0 X0)
       have r₂ := eq719 X0 x (k x (M.op X0 X0))
       grind)
    | (have r₁ := eq37476 X0
       have r₂ := eq719 y x x
       grind)
    | exact resolve eq37476 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq37476
  have eq37693 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k x (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq4699 X1 X0
       have i₂ := eq37552 (σ (M.op X0 X0))
       grind)
    | exact superpose eq37552 eq4699
    | exact resolve eq4699 eq37552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4699
  have eq37707 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2212 X0 x
       have i₂ := eq37552 x
       grind)
    | exact superpose eq37552 eq2212
    | (have j0 := eq2212 X0 x
       grind)
    | (have r₁ := eq2212 X0 x
       have r₂ := eq37552 x
       grind)
    | exact resolve eq2212 eq37552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212
  have eq37718 : ∀ X0 : G, x = (M.op X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq37707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37707
  have eq37736 : ∀ X0 : G, (k x x) = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq37718 eq37693
    | exact resolve eq37693 eq37718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37693
  have eq37755 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq37552 eq37736
    | exact resolve eq37736 eq37552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37552 eq37736
  have eq37767 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq37718 eq37755
    | exact resolve eq37755 eq37718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37755
  have eq37774 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq37767
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37767
    | exact resolve eq37767 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37767
  have eq37777 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq37774 eq31
    | exact resolve eq31 eq37774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37888 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq37777
    | exact resolve eq37777 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37777
  have eq37889 : x = (σ x) ∨ x = y := by grind
  clear eq37888
  have eq37906 : (M.op x y) = (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq37889
       grind)
    | exact superpose eq37889 eq18
    | exact resolve eq18 eq37889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37889
  have eq38483 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq37718 (M.op X0 X0)
       grind)
    | exact superpose eq37718 eq16
    | exact resolve eq16 eq37718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37718
  have eq38553 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq37774 eq38483
    | exact resolve eq38483 eq37774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37774 eq38483
  have eq40134 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq38553 eq37906
    | exact resolve eq37906 eq38553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37906
  have eq40137 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq38553 eq26
    | (have j1 := eq38553 (σ y)
       grind)
    | exact resolve eq26 eq38553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38553
  have eq40372 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq40134
  have eq41058 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq40137 eq27
    | exact resolve eq27 eq40137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40137
  have eq41121 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq40372 eq31
    | exact resolve eq31 eq40372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40372
  have eq41222 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq41121
    | exact resolve eq41121 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41121
  have eq41223 : y = (M.op x y) ∨ x = y := by grind
  clear eq41222
  have eq41264 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq41223
       grind)
    | exact superpose eq41223 eq24
    | exact resolve eq24 eq41223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41223
  have eq41318 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq41264
    | exact resolve eq41264 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41264
  have eq41380 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq41318 eq41058
    | (have r₁ := eq41058
       have r₂ := eq41318
       grind)
    | exact resolve eq41058 eq41318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41058 eq41318
  have eq41381 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq41380
  have eq41382 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq41381
  have eq41430 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq41382 eq31
    | exact resolve eq31 eq41382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq41382
  have eq41541 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq41430
    | exact resolve eq41430 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq41430
  have eq41542 : x = y := by grind
  clear eq41541
  have eq41584 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq41542
       grind)
    | exact superpose eq41542 eq18
    | exact resolve eq18 eq41542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq41585 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq41542
       grind)
    | exact superpose eq41542 eq24
    | exact resolve eq24 eq41542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq41542
  have eq41626 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41585
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41585
    | exact resolve eq41585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq41585
  have eq41633 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq41626 eq26
    | exact resolve eq26 eq41626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq41626
  have eq41766 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq698 x X0
       have i₂ := eq41584
       grind)
    | exact superpose eq41584 eq698
    | exact resolve eq698 eq41584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41824 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2220 X0 x
       have i₂ := eq41584
       grind)
    | exact superpose eq41584 eq2220
    | exact resolve eq2220 eq41584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220 eq41584
  have eq42076 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq20 eq41824
    | (have j0 := eq41824 X0
       grind)
    | exact resolve eq41824 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq41824
  have eq42188 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq42076 x
       have i₂ := eq41766 x
       grind)
    | exact superpose eq41766 eq42076
    | exact resolve eq42076 eq41766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42076
  have eq42691 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq41633 eq698
    | exact resolve eq698 eq41633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq41633
  have eq43040 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq42691 x
       have i₂ := eq41766 x
       grind)
    | exact superpose eq41766 eq42691
    | exact resolve eq42691 eq41766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41766 eq42691
  have eq43429 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq43040 eq27
    | exact resolve eq27 eq43040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq43040
  have eq43477 : False := by grind
  exact eq43477

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pxx_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  clear eq35
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq98 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq107 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq107 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq107 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq107 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq98
       have i₂ := eq108 sF3
       grind)
    | exact superpose eq108 eq98
    | exact resolve eq98 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq122 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq121
       have i₂ := eq108 y
       grind)
    | exact superpose eq108 eq121
    | exact resolve eq121 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq132
       have i₂ := eq108 sF1
       grind)
    | exact superpose eq108 eq132
    | exact resolve eq132 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq138 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq135
       have i₂ := eq108 sF0
       grind)
    | exact superpose eq108 eq135
    | exact resolve eq135 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq135
  have eq244 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq290 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (σ (k (M.op x y) (k (τ X0) X1))) = (k (σ (M.op x y)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq37
    | exact resolve eq37 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq37
  have eq425 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X2 X2) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq53 X0 X1 X3
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X2 X3 : G, (k X3 X2) = (M.op X3 X2) ∨ (M.op X2 X2) = X2 := by
    intro X2 X3
    first
    | (have j0 := eq433 x x X2 X3
       grind)
    | (have r₁ := eq433 x x X2 X3
       have r₂ := eq53 x x X2
       grind)
    | exact resolve eq433 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq465 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq138
       have i₂ := eq425 X0 sF0
       grind)
    | (have i₁ := eq138
       have i₂ := eq425 sF0 x
       grind)
    | exact superpose eq425 eq138
    | exact resolve eq138 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq440 X0 (M.op X0 X0)
       grind)
    | exact superpose eq440 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq440 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq506 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq517 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq515 X0 X1
       have i₂ := eq440 X0 X1
       grind)
    | exact superpose eq440 eq515
    | exact resolve eq515 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq532 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq52 X0 X0 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq52 X1 X0 X2 X4
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X1 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq738 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq290
    | exact resolve eq290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq441 (σ X1) X0
       grind)
    | exact superpose eq441 eq290
    | (have j1 := eq441 (σ X1) x
       grind)
    | exact resolve eq290 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq1086 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq441 y x
       grind)
    | exact superpose eq441 eq44
    | (have j1 := eq441 y x
       grind)
    | exact resolve eq44 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1086
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1086
    | exact resolve eq1086 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1107
    | exact resolve eq1107 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1107
  have eq1113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1109 eq441
    | (have j0 := eq441 (σ y) x
       grind)
    | exact resolve eq441 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1113
    | exact resolve eq1113 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1113
  have eq1118 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1115
       have r₂ := eq27
       grind)
    | exact resolve eq1115 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1122 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1118 eq122
    | exact resolve eq122 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq1118
  have eq1143 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1122
    | exact resolve eq1122 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1122
  have eq1144 : y = (M.op y y) := by grind
  clear eq1143
  have eq1145 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq1144
       have i₂ := eq425 X0 y
       grind)
    | (have i₁ := eq1144
       have i₂ := eq425 y X0
       grind)
    | exact superpose eq425 eq1144
    | exact resolve eq1144 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq1144
  have eq1223 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X0 X0 X1
       have i₂ := eq1145 (M.op X0 X0)
       grind)
    | exact superpose eq1145 eq52
    | exact resolve eq52 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1230 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq1145 sF0
       grind)
    | exact superpose eq1145 eq138
    | exact resolve eq138 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq1238 : y = (σ y) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq1145 sF1
       grind)
    | exact superpose eq1145 eq1230
    | exact resolve eq1230 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1242 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1223 X0 x
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq1223
    | exact resolve eq1223 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1259 : y = (σ y) := by
    first
    | (have i₁ := eq1238
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1238
    | exact resolve eq1238 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1278 : ∀ X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X1
    first
    | (have i₁ := eq244 x X1
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq244
    | exact resolve eq244 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq1279 : (σ x) = (M.op (M.op (σ y) y) (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | (have i₁ := eq1278 x
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq1278
    | exact resolve eq1278 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1280 : (σ x) = (M.op (M.op y y) (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | exact superpose eq1259 eq1279
    | exact resolve eq1279 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq1281 : (σ x) = (M.op (M.op (σ x) (σ y)) y) := by
    first
    | (have i₁ := eq1280
       have i₂ := eq440 y (M.op sF4 y)
       grind)
    | exact superpose eq440 eq1280
    | exact resolve eq1280 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1636 : ∀ X0 X1 : G, (k (σ (M.op x y)) (k X0 (σ X1))) = (σ (M.op (M.op x y) (k (τ X0) X1))) ∨ (k (τ X0) X1) = (M.op (k (τ X0) X1) (k (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq441 (k (τ X0) X1) sF0
       grind)
    | exact superpose eq441 eq293
    | (have j1 := eq441 (k (τ X0) X1) x
       grind)
    | exact resolve eq293 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq441
  have eq1651 : ∀ X0 X1 : G, (k (σ (M.op x y)) (k X0 (σ X1))) = (σ (M.op (M.op x y) (k (τ X0) X1))) ∨ y = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1636 X0 X1
       have i₂ := eq1145 (k (τ X0) X1)
       grind)
    | exact superpose eq1145 eq1636
    | (have j0 := eq1636 X0 X1
       grind)
    | exact resolve eq1636 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq3774 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) y)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq532 X0 X1 X2 x
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq532
    | exact resolve eq532 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq3775 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X0 y)) y)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq3774 X0 x X2
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq3774
    | exact resolve eq3774 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774
  have eq4253 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq540 X0 X1 X2 X3 x
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq540
    | exact resolve eq540 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq4254 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 y) (M.op X0 y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq4253 X0 X1 x X3
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq4253
    | exact resolve eq4253 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253
  have eq4255 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op (M.op X1 y) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq4254 X0 X1 x
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq4254
    | exact resolve eq4254 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254
  have eq4331 : ∀ X0 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq4255 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4255
    | (have j0 := eq4255 x X0
       grind)
    | exact resolve eq4255 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4351 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op (M.op X0 y) y))) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3775 (M.op X0 y) X1
       have i₂ := eq4255 (M.op X1 (M.op (M.op X0 y) y)) X0
       grind)
    | exact superpose eq4255 eq3775
    | exact resolve eq3775 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775 eq4255
  have eq4400 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4351 X0 X1
       have i₂ := eq1242 X0
       grind)
    | exact superpose eq1242 eq4351
    | exact resolve eq4351 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4351
  have eq4802 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq541 X0 X1 X2 X3 X4 x
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq541
    | exact resolve eq541 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq4803 : ∀ X0 X1 X4 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 y)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq4802 X0 X1 x x X4
       have i₂ := eq555 x (M.op X0 X1) x
       grind)
    | exact superpose eq555 eq4802
    | exact resolve eq4802 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq4802
  have eq4804 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X1) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq4803 X0 X1 x
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq4803
    | exact resolve eq4803 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq4892 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq1281 eq4804
    | exact resolve eq4804 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq4804
  have eq24387 : ∀ X0 X1 : G, (σ (M.op (M.op x y) (τ X0))) = (k (σ (M.op x y)) (k X0 (σ (M.op X1 X1)))) ∨ (τ X0) = y := by
    intro X0 X1
    first
    | (have i₁ := eq1651 X0 (M.op X0 X0)
       have i₂ := eq517 X0 (τ X0)
       grind)
    | exact superpose eq517 eq1651
    | exact resolve eq1651 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq24460 : ∀ X0 : G, (σ (M.op (M.op x y) (τ X0))) = (k (σ (M.op x y)) (k X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq24387 X0 x
       have i₂ := eq465 x
       grind)
    | exact superpose eq465 eq24387
    | (have j0 := eq24387 X0 x
       grind)
    | exact resolve eq24387 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq24387
  have eq24501 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (σ (M.op (M.op x y) (τ X0))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq24460 x
       have i₂ := eq517 sF1 x
       grind)
    | exact superpose eq517 eq24460
    | (have j0 := eq24460 X0
       grind)
    | exact resolve eq24460 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq24460
  have eq30187 : ∀ X0 : G, (τ (k (σ (M.op x y)) X0)) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = y := by
    intro X0
    first
    | exact superpose eq24501 eq16
    | (have j1 := eq24501 X0
       grind)
    | exact resolve eq16 eq24501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24501
  have eq32828 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ (k (σ (M.op x y)) X0)) (M.op X1 X1)) (M.op x y)) ∨ (τ X0) = y := by
    intro X0 X1
    first
    | exact superpose eq30187 eq14
    | (have j1 := eq30187 X0
       grind)
    | exact resolve eq14 eq30187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30187
  have eq32836 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (k (σ (M.op x y)) X0)) y) (M.op x y)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq32828 X0 x
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq32828
    | (have j0 := eq32828 X0 x
       grind)
    | exact resolve eq32828 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32828
  have eq32860 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (k (σ (M.op x y)) X0)) x) y) ∨ (τ X0) = y := by
    intro X0
    first
    | exact superpose eq4331 eq32836
    | (have j0 := eq32836 X0
       grind)
    | exact resolve eq32836 eq4331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4331 eq32836
  have eq60638 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq1068 X0 X1
       have i₂ := eq1145 (σ X1)
       grind)
    | exact superpose eq1145 eq1068
    | (have j0 := eq1068 X0 X1
       grind)
    | exact resolve eq1068 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq60756 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ (M.op (M.op (σ X1) X0) (M.op X2 X2))) X1) ∨ (σ X1) = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60638 (M.op (M.op (σ X1) X0) (M.op X2 X2)) X1
       have i₂ := eq14 X0 (σ X1) X2
       grind)
    | exact superpose eq14 eq60638
    | (have j0 := eq60638 X0 X1
       grind)
    | exact resolve eq60638 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60638
  have eq60965 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op (M.op (σ X1) X0) y)) X1) ∨ (σ X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq60756 X0 X1 x
       have i₂ := eq1145 x
       grind)
    | exact superpose eq1145 eq60756
    | (have j0 := eq60756 X0 X1 x
       grind)
    | exact resolve eq60756 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145 eq60756
  have eq200705 : ∀ X0 X1 : G, (τ X1) = (k (τ (M.op (M.op X0 X1) y)) (τ X0)) ∨ y = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq60965 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq60965
    | exact resolve eq60965 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60965
  have eq201655 : ∀ X0 X1 : G, (τ X1) = (τ (k (M.op (M.op X0 X1) y) X0)) ∨ y = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq200705 X0 X1
       have i₂ := eq738 X0 (M.op (M.op X0 X1) y)
       grind)
    | exact superpose eq738 eq200705
    | (have j0 := eq200705 X0 X1
       grind)
    | exact resolve eq200705 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq200705
  have eq223715 : ∀ X0 : G, (τ (σ x)) = (τ (k (M.op (M.op X0 y) y) (M.op (M.op (σ x) (σ y)) X0))) ∨ y = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq4892 eq201655
    | (have j0 := eq201655 (M.op (M.op (σ x) (σ y)) X0) x
       grind)
    | exact resolve eq201655 eq4892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4892 eq201655
  have eq225409 : ∀ X0 : G, (τ (σ x)) = (τ (k X0 (M.op (M.op (σ x) (σ y)) X0))) ∨ y = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq223715 X0
       have i₂ := eq1242 X0
       grind)
    | exact superpose eq1242 eq223715
    | (have j0 := eq223715 X0
       grind)
    | exact resolve eq223715 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223715
  have eq225697 : ∀ X0 : G, x = (τ (k X0 (M.op (M.op (σ x) (σ y)) X0))) ∨ y = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq28 eq225409
    | (have j0 := eq225409 X0
       grind)
    | exact resolve eq225409 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq225409
  have eq4165337 : (M.op (M.op x x) y) = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq225697 eq32860
    | (have j0 := eq32860 (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))
       have j1 := eq225697 (σ (M.op x y))
       grind)
    | exact resolve eq32860 eq225697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32860 eq225697
  have eq4165753 : y = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4165337
       have i₂ := eq440 x y
       grind)
    | exact superpose eq440 eq4165337
    | exact resolve eq4165337 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq4165337
  have eq4165754 : y = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
  clear eq4165753
  have eq4169698 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4165754 eq15
    | exact resolve eq15 eq4165754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4165754
  have eq4171829 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4169698
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4169698
    | exact resolve eq4169698 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4169698
  have eq4171965 : y = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1259 eq4171829
    | exact resolve eq4171829 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259 eq4171829
  have eq4171966 : y = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
  clear eq4171965
  have eq4172072 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) y) y) := by
    first
    | exact superpose eq4171966 eq4400
    | exact resolve eq4400 eq4171966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4400 eq4171966
  have eq4172111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4172072
       have i₂ := eq1242 sF1
       grind)
    | exact superpose eq1242 eq4172072
    | exact resolve eq4172072 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242 eq4172072
  have eq4172164 : False := by grind
  exact eq4172164

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = m(Y,Y) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_x_pxy_x_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq29 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq32 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq28 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28
    | (have j0 := eq28 x
       grind)
    | exact resolve eq28 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
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
  have eq42 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  clear eq29
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
  have eq52 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 y x X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ y) (σ x) X0
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq77 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq186 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 x x X1
       have i₂ := eq54 x x X0
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X2 ∨ (k X3 X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq54 X0 X1 X2
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op (M.op X1 X1) X0))
       have r₂ := eq54 X0 X1 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X2
       have i₂ := eq54 X0 X1 X2
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X2 X2) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X2
       have i₂ := eq54 X0 X1 X3
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq54 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq262 : ∀ X0 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 X0) ∨ (M.op X2 X2) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq249 X0 x X2 X3
       have i₂ := eq255 x X0
       grind)
    | exact superpose eq255 eq249
    | (have j0 := eq249 X0 x X2 X3
       grind)
    | (have r₁ := eq249 (M.op x x) x (M.op x x) X3
       have r₂ := eq255 x (M.op (M.op x x) (M.op x x))
       grind)
    | exact resolve eq249 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq263 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op X3 X3) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq248 X0 X1 X2 X3
       have i₂ := eq255 X1 X0
       grind)
    | exact superpose eq255 eq248
    | (have j0 := eq248 X0 X1 X2 X3
       grind)
    | (have r₁ := eq248 (M.op X1 X1) X1 X2 (M.op X1 X1)
       have r₂ := eq255 X1 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact resolve eq248 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq264 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X2 ∨ (k X3 X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq247 X0 x X2 X3
       have i₂ := eq255 x X0
       grind)
    | exact superpose eq255 eq247
    | (have j0 := eq247 X0 x X2 X3
       grind)
    | (have r₁ := eq247 (M.op X0 X0) x (M.op (M.op x x) (M.op X0 X0)) X3
       have r₂ := eq255 X0 (M.op (M.op x x) (M.op X0 X0))
       grind)
    | (have r₁ := eq247 X0 x (M.op (M.op X0 X0) (M.op X0 (M.op (M.op x x) X0))) X3
       have r₂ := eq255 X0 (M.op X0 (M.op (M.op x x) X0))
       grind)
    | exact resolve eq247 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq272 : ∀ X2 X3 : G, (k X3 X2) = (M.op X3 X2) ∨ (M.op X2 X2) = X2 := by
    intro X2 X3
    first
    | (have j0 := eq262 x X2 X3
       grind)
    | (have r₁ := eq262 x x X3
       have r₂ := eq245 x x
       grind)
    | (have r₁ := eq262 x x X3
       have r₂ := eq245 x x
       grind)
    | exact resolve eq262 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq273 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq263 X0 X1 X2 X3
       grind)
    | (have r₁ := eq263 X1 X1 X2 X0
       have r₂ := eq245 X0 X1
       grind)
    | (have r₁ := eq263 X0 X1 X2 X1
       have r₂ := eq245 X0 X1
       grind)
    | exact resolve eq263 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq278 : ∀ X0 X2 X3 : G, (M.op X0 X0) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq273 X0 x X2 X3
       have i₂ := eq255 x X0
       grind)
    | exact superpose eq255 eq273
    | (have j0 := eq273 X0 x X2 X3
       grind)
    | exact resolve eq273 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq308 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq255 X0 (M.op X0 X0)
       grind)
    | exact superpose eq255 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq255 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) X2
       have i₂ := eq255 X1 X0
       grind)
    | exact superpose eq255 eq9
    | exact resolve eq9 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq320 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X1 X1) X0
       have i₂ := eq315 X1 (σ X0)
       grind)
    | exact superpose eq315 eq48
    | exact resolve eq48 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (M.op X1 X1)
       have i₂ := eq315 X1 (τ X0)
       grind)
    | exact superpose eq315 eq49
    | exact resolve eq49 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq323 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq321
    | exact resolve eq321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq386 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ (M.op X1 X1)))
       have i₂ := eq320 X0 X1
       grind)
    | exact superpose eq320 eq10
    | exact resolve eq10 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq404 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq386
    | exact resolve eq386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq415 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ (τ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (τ (M.op X1 X1)) X0
       have i₂ := eq404 (σ X0) X1
       grind)
    | exact superpose eq404 eq48
    | exact resolve eq48 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq314 (M.op X0 (M.op X1 X1)) X3 x
       have i₂ := eq314 X0 x X1
       grind)
    | exact superpose eq314 eq314
    | exact resolve eq314 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ (τ (M.op X1 X1))))
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq10
    | exact resolve eq10 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq642 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq624
    | exact resolve eq624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq663 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq323 (σ (M.op X0 X0)) X0
       have i₂ := eq186 (σ (M.op X0 X0))
       grind)
    | exact superpose eq186 eq323
    | (have j1 := eq186 (σ (M.op X0 X0))
       grind)
    | exact resolve eq323 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq666 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq404 (τ (M.op X0 X0)) X0
       have i₂ := eq186 (τ (M.op X0 X0))
       grind)
    | exact superpose eq186 eq404
    | (have j1 := eq186 (τ (M.op X0 X0))
       grind)
    | exact resolve eq404 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq186 sF3
       grind)
    | exact superpose eq186 eq68
    | (have j1 := eq186 (σ y)
       grind)
    | exact resolve eq68 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq670 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq666 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq673 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq692 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq53 X1 X0 X2 X4
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq729 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X3)) = (M.op (M.op X0 (M.op X4 X4)) (M.op X1 (M.op X2 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X3 X3)) (M.op X1 (M.op X2 X2)) X4
       have i₂ := eq53 X1 X0 X3 X2
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq735 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq701 X0 X1 x x X4 X5
       have i₂ := eq314 (M.op X0 X1) x x
       grind)
    | exact superpose eq314 eq701
    | exact resolve eq701 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq760 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op X0 X0))) (τ (τ (M.op X0 X0)))) ∨ (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op X0 X0))) (τ (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq186 (τ (τ (M.op X0 X0)))
       have i₂ := eq642 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq642 eq186
    | (have j0 := eq186 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq186 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq642
  have eq764 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op X0 X0))) (τ (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq760 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq829 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 X0
       have i₂ := eq272 X1 (σ X0)
       grind)
    | exact superpose eq272 eq48
    | (have j1 := eq272 X1 x
       grind)
    | exact resolve eq48 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq272 X1 (τ X0)
       grind)
    | exact superpose eq272 eq49
    | (have j1 := eq272 X1 x
       grind)
    | exact resolve eq49 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq272 X1 X0
       grind)
    | exact superpose eq272 eq128
    | (have j1 := eq272 X1 x
       grind)
    | exact resolve eq128 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq272 (σ X1) (σ X0)
       grind)
    | exact superpose eq272 eq15
    | (have j1 := eq272 (σ X1) x
       grind)
    | exact resolve eq15 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq272 sF2 (σ X0)
       grind)
    | exact superpose eq272 eq31
    | (have j1 := eq272 (σ x) x
       grind)
    | exact resolve eq31 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq850 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35
       have i₂ := eq272 sF2 sF1
       grind)
    | exact superpose eq272 eq35
    | (have j1 := eq272 (σ x) x
       grind)
    | exact resolve eq35 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq855 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq42
       have i₂ := eq272 sF3 sF2
       grind)
    | exact superpose eq272 eq42
    | (have j1 := eq272 (σ y) x
       grind)
    | exact resolve eq42 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq859 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq855
    | exact resolve eq855 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq861 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq859
       have i₂ := eq272 y x
       grind)
    | exact superpose eq272 eq859
    | (have j1 := eq272 (σ y) x
       grind)
    | exact resolve eq859 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq859
  have eq872 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq861
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq861
    | exact resolve eq861 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq872
    | exact resolve eq872 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq874 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq873
       have r₂ := eq27
       grind)
    | exact resolve eq873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq894 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq874 eq404
    | exact resolve eq404 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq874
  have eq903 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39 eq894
    | exact resolve eq894 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq905 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq903 X0
       have j1 := eq12 X0 y
       grind)
    | (have r₁ := eq903 X0
       have r₂ := eq12 X0 y
       grind)
    | exact resolve eq903 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq921 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq669
       have i₂ := eq905 y
       grind)
    | exact superpose eq905 eq669
    | exact resolve eq669 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq905
  have eq929 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq921
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq921
    | exact resolve eq921 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq921
  have eq930 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq929
  have eq957 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ y)) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq930 eq9
    | exact resolve eq9 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq930 eq245
    | exact resolve eq245 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq966 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq930 eq255
    | exact resolve eq255 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq967 : ∀ X0 X1 : G, (σ y) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq930 eq264
    | (have j0 := eq264 X0 X0 X1
       grind)
    | (have r₁ := eq264 (σ y) (σ y) x
       have r₂ := eq930
       grind)
    | exact resolve eq264 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq969 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (σ y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq930 eq314
    | exact resolve eq314 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq977 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq930 eq451
    | exact resolve eq451 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq930
  have eq987 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (σ y))) (M.op X3 X3))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq692 X0 x X2 X3
       have i₂ := eq977 X0 x
       grind)
    | exact superpose eq977 eq692
    | exact resolve eq692 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq988 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X3)) = (M.op (M.op X0 (M.op X4 X4)) (M.op X1 (σ y))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq729 X0 X1 x X3 X4
       have i₂ := eq977 X1 x
       grind)
    | exact superpose eq977 eq729
    | exact resolve eq729 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq989 : ∀ X0 X1 X5 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) = (M.op X1 (σ y)) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq735 X0 X1 x X5
       have i₂ := eq977 X1 x
       grind)
    | exact superpose eq977 eq735
    | exact resolve eq735 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq995 : ∀ X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (σ y)) (M.op y (M.op X2 X2))) := by
    intro X1 X2
    first
    | (have i₁ := eq702 x X1 X2
       have i₂ := eq977 x x
       grind)
    | exact superpose eq977 eq702
    | exact resolve eq702 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq1001 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq77 X0 x
       have i₂ := eq977 sF3 x
       grind)
    | exact superpose eq977 eq77
    | exact resolve eq77 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1005 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq969 X0 x
       have i₂ := eq977 X0 x
       grind)
    | exact superpose eq977 eq969
    | exact resolve eq969 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq977
  have eq1022 : ∀ X2 X3 : G, (σ y) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X2 X3
    first
    | (have i₁ := eq278 x X2 X3
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq278
    | (have j0 := eq278 x X2 X3
       grind)
    | exact resolve eq278 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq1031 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq670 x
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq670
    | exact resolve eq670 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq1034 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) := by
    first
    | (have i₁ := eq673 x
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq673
    | exact resolve eq673 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq1037 : (τ (τ (σ y))) = (M.op (τ (τ (σ y))) (τ (τ (σ y)))) := by
    first
    | (have i₁ := eq764 x
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq764
    | exact resolve eq764 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq1040 : ∀ X0 X1 : G, (σ y) = X1 ∨ (σ (k X0 (τ X1))) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq965 X1
       grind)
    | exact superpose eq965 eq829
    | (have j0 := eq829 X0 X1
       grind)
    | exact resolve eq829 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq1041 : ∀ X0 X1 : G, (σ y) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq830 X0 X1
       have i₂ := eq965 X1
       grind)
    | exact superpose eq965 eq830
    | (have j0 := eq830 X0 X1
       grind)
    | exact resolve eq830 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq1042 : ∀ X0 X1 : G, (σ y) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq831 X0 X1
       have i₂ := eq965 X1
       grind)
    | exact superpose eq965 eq831
    | (have j0 := eq831 X0 X1
       grind)
    | exact resolve eq831 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq1049 : ∀ X0 X1 : G, (σ X1) = (σ y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq838 X0 X1
       have i₂ := eq965 (σ X1)
       grind)
    | exact superpose eq965 eq838
    | (have j0 := eq838 X0 X1
       grind)
    | exact resolve eq838 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq1067 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq849 X0
       have i₂ := eq965 sF2
       grind)
    | exact superpose eq965 eq849
    | (have j0 := eq849 X0
       grind)
    | exact resolve eq849 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq1068 : (σ x) = (σ y) ∨ (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq850
       have i₂ := eq965 sF2
       grind)
    | exact superpose eq965 eq850
    | exact resolve eq850 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq1073 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq1001 x
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq1001
    | exact resolve eq1001 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1078 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (σ y)) (M.op y (σ y))) := by
    intro X1
    first
    | (have i₁ := eq995 X1 x
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq995
    | exact resolve eq995 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1083 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 X1) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1 x
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq989
    | exact resolve eq989 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1084 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) (M.op X3 X3)) = (M.op (M.op X0 (σ y)) (M.op X1 (σ y))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq988 X0 X1 X3 x
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq988
    | exact resolve eq988 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1085 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (σ y))) (σ y))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq987 X0 X2 x
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq987
    | exact resolve eq987 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1098 : (σ y) = (τ (τ (σ y))) := by
    first
    | (have i₁ := eq1037
       have i₂ := eq965 (τ (τ sF3))
       grind)
    | exact superpose eq965 eq1037
    | exact resolve eq1037 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1101 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq1034
       have i₂ := eq965 (σ sF3)
       grind)
    | exact superpose eq965 eq1034
    | exact resolve eq1034 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1104 : (σ y) = (τ (σ y)) := by
    first
    | (have i₁ := eq1031
       have i₂ := eq965 (τ sF3)
       grind)
    | exact superpose eq965 eq1031
    | exact resolve eq1031 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1112 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq966 eq1073
    | exact resolve eq1073 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1115 : (M.op (M.op x y) (σ y)) = (M.op (M.op x (σ y)) (M.op y (σ y))) := by
    first
    | (have i₁ := eq1078 x
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq1078
    | exact resolve eq1078 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1116 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 (σ y)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1084 X0 X1 x
       have i₂ := eq965 x
       grind)
    | exact superpose eq965 eq1084
    | exact resolve eq1084 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965 eq1084
  have eq1120 : (σ y) = (τ y) := by
    first
    | exact superpose eq39 eq1098
    | exact resolve eq1098 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1128 : y = (σ y) := by
    first
    | exact superpose eq39 eq1104
    | exact resolve eq1104 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1104
  have eq1130 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq966 eq1112
    | exact resolve eq1112 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1132 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 (σ y)) (M.op (M.op X0 (σ y)) (σ y)))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq1116 eq1085
    | exact resolve eq1085 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1134 : (M.op (M.op x y) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq1116 eq1115
    | exact resolve eq1115 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1144 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1128 eq26
    | exact resolve eq26 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1150 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1128 eq957
    | exact resolve eq957 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1154 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq1128 eq966
    | exact resolve eq966 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq1155 : ∀ X0 X1 : G, y ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1128 eq967
    | (have j0 := eq967 X0 X1
       grind)
    | (have r₁ := eq967 y X1
       have r₂ := eq1128
       grind)
    | exact resolve eq967 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq1157 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
    intro X0
    first
    | exact superpose eq1128 eq1005
    | exact resolve eq1005 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1158 : ∀ X2 X3 : G, (k X3 X2) = (M.op X3 X2) ∨ y = X2 := by
    intro X2 X3
    first
    | exact superpose eq1128 eq1022
    | (have j0 := eq1022 X2 X3
       grind)
    | exact resolve eq1022 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1159 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ y = X1 := by
    intro X0 X1
    first
    | exact superpose eq1128 eq1040
    | (have j0 := eq1040 X0 X1
       grind)
    | exact resolve eq1040 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1160 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ y = X1 := by
    intro X0 X1
    first
    | exact superpose eq1128 eq1041
    | (have j0 := eq1041 X0 X1
       grind)
    | exact resolve eq1041 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1161 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ y = X1 := by
    intro X0 X1
    first
    | exact superpose eq1128 eq1042
    | (have j0 := eq1042 X0 X1
       grind)
    | exact resolve eq1042 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1162 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = y := by
    intro X0 X1
    first
    | exact superpose eq1128 eq1049
    | (have j0 := eq1049 X0 X1
       grind)
    | exact resolve eq1049 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1168 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ y = (σ x) := by
    intro X0
    first
    | exact superpose eq1128 eq1067
    | (have j0 := eq1067 X0
       grind)
    | exact resolve eq1067 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1169 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (σ x) := by
    first
    | exact superpose eq1128 eq1068
    | exact resolve eq1068 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1171 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X1) (M.op X0 y)) := by
    intro X0 X1
    first
    | exact superpose eq1128 eq1083
    | exact resolve eq1083 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1177 : y = (σ y) := by
    first
    | exact superpose eq1128 eq1101
    | exact resolve eq1101 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 y) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq1128 eq1116
    | exact resolve eq1116 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1179 : y = (τ y) := by
    first
    | exact superpose eq1128 eq1120
    | exact resolve eq1120 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1182 : (σ x) = (M.op (M.op (σ x) (σ y)) y) := by
    first
    | exact superpose eq1128 eq1130
    | exact resolve eq1130 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1183 : (M.op (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1128 eq1134
    | exact resolve eq1134 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1185 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 y) (M.op (M.op X0 y) y))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq1128 eq1132
    | exact resolve eq1132 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq1132
  have eq1199 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1183
       have i₂ := eq1157 x
       grind)
    | exact superpose eq1157 eq1183
    | (have j1 := eq1157 x
       grind)
    | exact resolve eq1183 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1201 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 y) X0)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1185 X0 X2
       have i₂ := eq1157 X0
       grind)
    | exact superpose eq1157 eq1185
    | exact resolve eq1185 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1290 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1201 X1 (M.op X0 y)
       have i₂ := eq1157 X0
       grind)
    | exact superpose eq1157 eq1201
    | exact resolve eq1201 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : ∀ X0 : G, x = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1201 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1201
    | (have j0 := eq1201 X0 x
       grind)
    | exact resolve eq1201 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1293 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1199 eq1201
    | exact resolve eq1201 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1294 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1144 eq1201
    | exact resolve eq1201 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1182 eq1201
    | exact resolve eq1201 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1407 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0
    first
    | exact superpose eq1199 eq1171
    | exact resolve eq1171 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1409 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq1182 eq1171
    | exact resolve eq1171 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1705 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq1178 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1178
    | (have j0 := eq1178 X0 x
       grind)
    | exact resolve eq1178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1708 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 y) (M.op X1 y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1171 (M.op X0 X1) X2
       have i₂ := eq1178 X0 X1
       grind)
    | exact superpose eq1178 eq1171
    | exact resolve eq1171 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1924 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1150 X1 X2
       have i₂ := eq1290 (M.op X1 X2) X0
       grind)
    | exact superpose eq1290 eq1150
    | exact resolve eq1150 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq2397 : (M.op (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) ∨ y = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1169
       have i₂ := eq1158 x sF0
       grind)
    | exact superpose eq1158 eq1169
    | (have j1 := eq1158 (σ x) x
       grind)
    | exact resolve eq1169 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq3016 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 x) y)) = X0 := by
    intro X0
    first
    | exact superpose eq1705 eq1201
    | exact resolve eq1201 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq1705
  have eq3053 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op X1 x) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3016 X1
       have i₂ := eq1290 (M.op X1 x) X0
       grind)
    | exact superpose eq1290 eq3016
    | exact resolve eq3016 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290 eq3016
  have eq9064 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq1159 X0 X1
       grind)
    | exact superpose eq1159 eq10
    | (have j1 := eq1159 X0 X1
       grind)
    | exact resolve eq10 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq9127 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = y := by
    intro X0 X1
    first
    | (have i₁ := eq1160 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1160
    | (have j0 := eq1160 X0 (τ X0)
       grind)
    | exact resolve eq1160 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq13982 : ∀ X0 : G, (τ x) = (k (τ X0) (τ (M.op (M.op x y) X0))) ∨ y = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1291 eq1161
    | (have j0 := eq1161 X0 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq1161 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161 eq1291
  have eq14091 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq9064 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9064
    | (have j0 := eq9064 x X0
       grind)
    | exact resolve eq9064 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9064
  have eq14160 : (τ (σ x)) = (k x (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1294 eq14091
    | (have j0 := eq14091 (M.op (M.op (σ x) (σ y)) (σ x))
       grind)
    | exact resolve eq14091 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14091
  have eq14203 : x = (k x (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq38 eq14160
    | exact resolve eq14160 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14160
  have eq15700 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X1 (M.op x y)) X0) (M.op (M.op X1 y) x)) := by
    intro X0 X1
    first
    | exact superpose eq1199 eq1708
    | exact resolve eq1708 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708
  have eq17692 : (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq14203 eq48
    | exact resolve eq48 eq14203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq14203
  have eq17727 : (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have j1 := eq1155 (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)
       grind)
    | (have r₁ := eq17692
       have r₂ := eq1155 (M.op (M.op (σ x) (σ y)) (σ x)) x
       grind)
    | exact resolve eq17692 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17692
  have eq17735 : (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq17727
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17727
    | exact resolve eq17727 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17727
  have eq17752 : (τ (σ x)) = (k (τ (σ x)) (τ (M.op (M.op (σ x) (σ y)) (σ x)))) := by
    first
    | exact superpose eq17735 eq128
    | exact resolve eq128 eq17735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17735
  have eq17753 : x = (k x (τ (M.op (M.op (σ x) (σ y)) (σ x)))) := by
    first
    | exact superpose eq38 eq17752
    | exact resolve eq17752 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17752
  have eq17778 : x = (M.op x (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq17753 eq1158
    | (have j0 := eq1158 (τ (M.op (M.op (σ x) (σ y)) (σ x))) x
       grind)
    | exact resolve eq1158 eq17753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq17753
  have eq23238 : (M.op (M.op x y) x) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq2397 eq10
    | exact resolve eq10 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq23300 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq38 eq9127
    | exact resolve eq9127 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9127
  have eq28650 : (k (M.op (σ (M.op x y)) (σ x)) (σ x)) = (σ (M.op (M.op (M.op x y) x) x)) ∨ x = y ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq23238 eq23300
    | exact resolve eq23300 eq23238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23300
  have eq28651 : (k (M.op (σ (M.op x y)) (σ x)) (σ x)) = (σ (M.op (M.op (M.op x y) x) x)) ∨ x = y ∨ y = (σ x) := by grind
  clear eq28650
  have eq28664 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ x)) (σ x)) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq1407 eq28651
    | exact resolve eq28651 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407 eq28651
  have eq28672 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ x)) (σ x)) ∨ x = y ∨ y = (σ x) := by
    first
    | (have i₁ := eq28664
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28664
    | exact resolve eq28664 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28664
  have eq28676 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ x)) (σ x)) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq20 eq28672
    | exact resolve eq28672 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28672
  have eq28678 : (τ (σ (M.op x y))) = (k (τ (M.op (σ (M.op x y)) (σ x))) (τ (σ x))) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq28676 eq128
    | exact resolve eq128 eq28676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq28676
  have eq28701 : (τ (σ (M.op x y))) = (k (τ (M.op (σ (M.op x y)) (σ x))) x) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq38 eq28678
    | exact resolve eq28678 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28678
  have eq28702 : (M.op x y) = (k (τ (M.op (σ (M.op x y)) (σ x))) x) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq37 eq28701
    | exact resolve eq28701 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq28701
  have eq39076 : (M.op x y) = (k (M.op (M.op x y) x) x) ∨ x = y ∨ y = (σ x) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq23238 eq28702
    | exact resolve eq28702 eq23238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23238 eq28702
  have eq39117 : (M.op x y) = (k (M.op (M.op x y) x) x) ∨ x = y ∨ y = (σ x) := by grind
  clear eq39076
  have eq39177 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) x)) (σ x)) ∨ y = (σ x) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq39117 eq1168
    | exact resolve eq1168 eq39117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq39117
  have eq39200 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) x)) (σ x)) ∨ y = (σ x) ∨ x = y := by grind
  clear eq39177
  have eq39214 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) x)) (σ x)) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq39200
    | exact resolve eq39200 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39200
  have eq54430 : ∀ X0 : G, (τ (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op X0 (M.op x X0)) x) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq17778 eq1924
    | exact resolve eq1924 eq17778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17778
  have eq54488 : (M.op (M.op x y) x) = (τ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq54430 x
       have i₂ := eq1293 x
       grind)
    | exact superpose eq1293 eq54430
    | exact resolve eq54430 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293 eq54430
  have eq88882 : y = (τ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq54488 eq11
    | exact resolve eq11 eq54488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54488
  have eq127451 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq88882 eq11
    | exact resolve eq11 eq88882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88882
  have eq127638 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq127451
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq127451
    | exact resolve eq127451 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127451
  have eq127681 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (σ x) ∨ x = y ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq127638 eq39214
    | exact resolve eq39214 eq127638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127638
  have eq127750 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ x) ∨ x = y ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1409 eq127681
    | exact resolve eq127681 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq127681
  have eq127757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ x = y ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1144 eq127750
    | exact resolve eq127750 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127750
  have eq127758 : y = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ y = (σ x) := by
    first
    | (have r₁ := eq127757
       have r₂ := eq27
       grind)
    | exact resolve eq127757 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127757
  have eq127795 : (σ x) = (M.op (σ x) y) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq127758 eq1294
    | exact resolve eq1294 eq127758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq127758
  have eq127970 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq1144 eq127795
    | exact resolve eq127795 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127795
  have eq128074 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq127970 eq27
    | exact resolve eq27 eq127970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127970
  have eq419688 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x (M.op x y)) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq15700 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15700
    | (have j0 := eq15700 X0 x
       grind)
    | exact resolve eq15700 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15700
  have eq419993 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) (M.op X0 y)) (M.op x (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq419688 eq1924
    | exact resolve eq1924 eq419688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924 eq419688
  have eq420595 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq419993 (M.op X0 y)
       have i₂ := eq1157 X0
       grind)
    | exact superpose eq1157 eq419993
    | exact resolve eq419993 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157 eq419993
  have eq461152 : ∀ X0 : G, (σ (τ x)) = (k X0 (σ (τ (M.op (M.op x y) X0)))) ∨ y = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq13982 eq49
    | (have j1 := eq13982 X0
       grind)
    | exact resolve eq49 eq13982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq13982
  have eq461154 : ∀ X0 : G, (σ (τ x)) = (k X0 (M.op (M.op x y) X0)) ∨ y = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq461152 X0
       have i₂ := eq11 (M.op sF0 X0)
       grind)
    | exact superpose eq11 eq461152
    | (have j0 := eq461152 X0
       grind)
    | exact resolve eq461152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461152
  have eq461165 : ∀ X0 : G, x = (k X0 (M.op (M.op x y) X0)) ∨ y = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq461154 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq461154
    | (have j0 := eq461154 X0
       grind)
    | exact resolve eq461154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461154
  have eq461171 : ∀ X0 X1 : G, x = (k (M.op X1 (M.op (M.op X0 x) X1)) X0) ∨ y = X0 := by
    intro X0 X1
    first
    | exact superpose eq3053 eq461165
    | exact resolve eq461165 eq3053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3053 eq461165
  have eq470301 : x = (k (M.op (M.op x (M.op x y)) (M.op x y)) (M.op (M.op x y) x)) ∨ y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq420595 eq461171
    | (have j0 := eq461171 (M.op (M.op x y) x) x
       grind)
    | exact resolve eq461171 eq420595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420595 eq461171
  have eq470534 : x = (k (M.op (M.op x y) y) (M.op (M.op x y) x)) ∨ y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq470301
       have i₂ := eq1171 x sF0
       grind)
    | exact superpose eq1171 eq470301
    | exact resolve eq470301 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171 eq470301
  have eq470586 : x = (k x (M.op (M.op x y) x)) ∨ y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1199 eq470534
    | exact resolve eq470534 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq470534
  have eq470602 : x = (k x (M.op (M.op x y) x)) := by
    first
    | (have j1 := eq1155 (M.op (M.op x y) x) x
       grind)
    | (have r₁ := eq470586
       have r₂ := eq1155 (M.op (M.op x y) x) x
       grind)
    | exact resolve eq470586 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq470586
  have eq470792 : (σ x) = (M.op (σ x) (σ (M.op (M.op x y) x))) ∨ y = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq470602 eq1162
    | (have j0 := eq1162 x (M.op (M.op x y) x)
       grind)
    | exact resolve eq1162 eq470602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq470602
  have eq470806 : (σ x) = (M.op (σ x) (σ (M.op (M.op x y) x))) ∨ y = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq470792
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq470792
    | exact resolve eq470792 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470792
  have eq491480 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (M.op x y) x)) (σ x)) ∨ y = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq470806 eq1295
    | exact resolve eq1295 eq470806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295 eq470806
  have eq496544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ x = y ∨ y = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq491480 eq39214
    | exact resolve eq39214 eq491480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491480
  have eq496561 : y = (σ (M.op (M.op x y) x)) ∨ x = y ∨ y = (σ x) := by
    first
    | (have r₁ := eq496544
       have r₂ := eq27
       grind)
    | exact resolve eq496544 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496544
  have eq496570 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (σ x) ∨ x = y ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq496561 eq39214
    | exact resolve eq39214 eq496561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39214 eq496561
  have eq496585 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (σ x) ∨ x = y := by grind
  clear eq496570
  have eq496599 : (σ (M.op x y)) = (σ x) ∨ y = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq496585
       have i₂ := eq1154 sF2
       grind)
    | exact superpose eq1154 eq496585
    | exact resolve eq496585 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496585
  have eq496602 : y = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq496599
       have r₂ := eq128074
       grind)
    | exact resolve eq496599 eq128074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128074 eq496599
  have eq496606 : x = (τ y) ∨ x = y := by
    first
    | exact superpose eq496602 eq38
    | exact resolve eq38 eq496602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq496602
  have eq497095 : x = y ∨ x = y := by
    first
    | (have i₁ := eq496606
       have i₂ := eq1179
       grind)
    | exact superpose eq1179 eq496606
    | exact resolve eq496606 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq496606
  have eq497096 : x = y := by grind
  clear eq497095
  have eq497239 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq497096
       grind)
    | exact superpose eq497096 eq18
    | exact resolve eq18 eq497096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq497242 : (M.op (σ x) (σ y)) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq1144
       have i₂ := eq497096
       grind)
    | exact superpose eq497096 eq1144
    | exact resolve eq1144 eq497096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq497245 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1154 X0
       have i₂ := eq497096
       grind)
    | exact superpose eq497096 eq1154
    | exact resolve eq1154 eq497096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq497262 : x = (σ x) := by
    first
    | (have i₁ := eq1177
       have i₂ := eq497096
       grind)
    | exact superpose eq497096 eq1177
    | exact resolve eq1177 eq497096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq497096
  have eq572979 : x = (σ x) := by
    first
    | (have i₁ := eq497262
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq497262
    | exact resolve eq497262 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497262
  have eq576855 : x = (M.op x y) := by
    first
    | (have i₁ := eq497239
       have i₂ := eq497245 x
       grind)
    | exact superpose eq497245 eq497239
    | exact resolve eq497239 eq497245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497239
  have eq589248 : x = (σ x) := by
    first
    | exact superpose eq572979 eq22
    | exact resolve eq22 eq572979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq589254 : (M.op (σ x) (σ y)) = (M.op x x) := by
    first
    | exact superpose eq572979 eq497242
    | exact resolve eq497242 eq572979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497242 eq572979
  have eq598449 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq576855 eq20
    | exact resolve eq20 eq576855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq576855
  have eq610971 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq589254
       have i₂ := eq497245 x
       grind)
    | exact superpose eq497245 eq589254
    | exact resolve eq589254 eq497245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497245 eq589254
  have eq618901 : x = (σ (M.op x y)) := by
    first
    | (have i₁ := eq598449
       have i₂ := eq589248
       grind)
    | exact superpose eq589248 eq598449
    | exact resolve eq598449 eq589248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589248 eq598449
  have eq624859 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq610971 eq27
    | exact resolve eq27 eq610971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq610971
  have eq634784 : False := by grind
  exact eq634784

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_x_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq95 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq528 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ X2 = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq56 X0 X1 X3
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X2 X3 : G, (k X2 X3) = (M.op X3 X2) ∨ X2 = X3 := by
    intro X2 X3
    first
    | (have j0 := eq528 x x X2 X3
       grind)
    | (have r₁ := eq528 x x X2 X3
       have r₂ := eq56 x x X2
       grind)
    | exact resolve eq528 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq528
  have eq1377 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq536 y x
       grind)
    | exact superpose eq536 eq95
    | (have j1 := eq536 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq95 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1395 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1377
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1377
    | exact resolve eq1377 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1396 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq1395
    | exact resolve eq1395 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq1402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1396 eq536
    | (have j0 := eq536 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq536 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq1396
  have eq1409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1402
    | exact resolve eq1402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1418 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1409
       have r₂ := eq28
       grind)
    | exact resolve eq1409 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1424 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1418 eq30
    | exact resolve eq30 eq1418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1418
  have eq1442 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1424
    | exact resolve eq1424 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1424
  have eq1443 : x = y := by grind
  clear eq1442
  have eq1446 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1443
       grind)
    | exact superpose eq1443 eq19
    | exact resolve eq19 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1447 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1443
       grind)
    | exact superpose eq1443 eq25
    | exact resolve eq25 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1443
  have eq1463 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1447
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1447
    | exact resolve eq1447 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1447
  have eq1466 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1463 eq27
    | exact resolve eq27 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1463
  have eq1535 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1466 eq68
    | exact resolve eq68 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1466
  have eq1565 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1535
       have i₂ := eq1446
       grind)
    | exact superpose eq1446 eq1535
    | exact resolve eq1535 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446 eq1535
  have eq1566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1565 eq15
    | exact resolve eq15 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1566
    | exact resolve eq1566 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1566
  have eq1590 : False := by grind
  exact eq1590

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pyx_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq33
    | (have j0 := eq33 X0 X1 x
       grind)
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq69 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op X1 X1)) (σ X0)) := by
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
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2
       have i₂ := eq25 X0 X1 (σ X2)
       grind)
    | exact superpose eq25 eq22
    | exact resolve eq22 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq97 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq103 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq89 X0 x X2
       have i₂ := eq97 x X0
       grind)
    | exact superpose eq97 eq89
    | exact resolve eq89 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq97
  have eq301 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq43
    | (have j0 := eq43 X0 X1
       have j1 := eq40 (σ (M.op X0 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq43 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43
  have eq3242 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq301 x y
       grind)
    | exact superpose eq301 eq16
    | (have j1 := eq301 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq301 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq301 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq301 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq3281 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3242
  have eq3853 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) (M.op X0 X0)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq3281
       grind)
    | exact superpose eq3281 eq9
    | exact resolve eq9 eq3281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281
  have eq3893 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3853 x
       have i₂ := eq69 x x
       grind)
    | exact superpose eq69 eq3853
    | exact resolve eq3853 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3853
  have eq3894 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3893
  have eq9246 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3894
       grind)
    | exact superpose eq3894 eq10
    | exact resolve eq10 eq3894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3894
  have eq9289 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9246
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9246
    | exact resolve eq9246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9246
  have eq9290 : x = y := by grind
  clear eq9289
  have eq13300 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9290
       grind)
    | exact superpose eq9290 eq16
    | exact resolve eq16 eq9290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9290
  have eq13301 : False := by grind
  exact eq13301

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_x_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq62 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  have eq63 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (k y x) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22 eq36
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq84 y x
       grind)
    | exact superpose eq84 eq90
    | (have j1 := eq84 y x
       grind)
    | exact resolve eq90 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq122
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq124
  have eq194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq84
    | (have j0 := eq84 (σ y) (σ x)
       grind)
    | exact resolve eq84 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq194
    | exact resolve eq194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq198 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq195
       have r₂ := eq27
       grind)
    | exact resolve eq195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq200 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq198
    | exact resolve eq198 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq200 eq27
    | exact resolve eq27 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq200 eq76
    | (have r₁ := eq76
       have r₂ := eq200
       grind)
    | exact resolve eq76 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq379 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq378
  have eq382 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq379 eq125
    | exact resolve eq125 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq386 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq382
  have eq391 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq386
       have r₂ := eq202
       grind)
    | exact resolve eq386 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq386
  have eq394 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq391 eq63
    | exact resolve eq63 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq391
  have eq417 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq394
       have r₂ := eq200
       grind)
    | exact resolve eq394 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq394
  have eq480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq417 eq125
    | exact resolve eq125 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq417
  have eq483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq480
  have eq487 : y = (M.op x y) := by
    first
    | (have r₁ := eq483
       have r₂ := eq27
       grind)
    | exact resolve eq483 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq489 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq487 eq20
    | exact resolve eq20 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq492 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq487 eq75
    | (have r₁ := eq75
       have r₂ := eq487
       grind)
    | exact resolve eq75 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq497 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq492
  have eq503 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq489
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq489
    | exact resolve eq489 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq506 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq503 eq26
    | exact resolve eq26 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq658 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq497
       grind)
    | exact superpose eq497 eq90
    | exact resolve eq90 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq665 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq503 eq658
    | exact resolve eq658 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq667 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq665
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq665
    | exact resolve eq665 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq668 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq503 eq667
    | exact resolve eq667 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq683 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq668 eq84
    | (have j0 := eq84 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq84 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq684 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq683
  have eq686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq506 eq684
    | exact resolve eq684 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq689 : y = (M.op x x) := by
    first
    | (have r₁ := eq686
       have r₂ := eq27
       grind)
    | exact resolve eq686 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq694 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq62
       have i₂ := eq689
       grind)
    | exact superpose eq689 eq62
    | exact resolve eq62 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq689
  have eq708 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq694
       have r₂ := eq487
       grind)
    | exact resolve eq694 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq710 : y = (k y x) := by
    first
    | exact superpose eq487 eq708
    | exact resolve eq708 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq708
  have eq754 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq710
       grind)
    | exact superpose eq710 eq90
    | exact resolve eq90 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq710
  have eq761 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq503 eq754
    | exact resolve eq754 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq763 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq761
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq761
    | exact resolve eq761 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq761
  have eq764 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq503 eq763
    | exact resolve eq763 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq763
  have eq767 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq764 eq84
    | (have j0 := eq84 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq84 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq764
  have eq768 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq767
  have eq770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq506 eq768
    | exact resolve eq768 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq768
  have eq773 : False := by grind
  exact eq773

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq20 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq20 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq38 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq44 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq44
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq49
  have eq99 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq103 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       have j1 := eq52 X1 X0
       grind)
    | (have r₁ := eq99 X1 X1
       have r₂ := eq52 X1 X1
       grind)
    | (have r₁ := eq99 X1 X0
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq99 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq99
  have eq246 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq103 (σ X1) (σ X0)
       grind)
    | exact superpose eq103 eq15
    | exact resolve eq15 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 X0 X1
       have i₂ := eq103 X1 X0
       grind)
    | exact superpose eq103 eq246
    | exact resolve eq246 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq246
  have eq256 : False := by grind
  exact eq256

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pyx_pxx_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq62 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq13
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq13
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq55
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq69
  have eq72 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq60 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq60
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq77 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq74
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq62 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq62
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq81 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq78
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq94 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op y x) ∨ (k x y) = (M.op x x) := by
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
  have eq96 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq98 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq98 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq98 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq99 (σ X0)
       grind)
    | exact superpose eq99 eq10
    | exact resolve eq10 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq99 x
       grind)
    | exact superpose eq99 eq43
    | exact resolve eq43 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq103 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq99 sF2
       grind)
    | exact superpose eq99 eq102
    | exact resolve eq102 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq101 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq101
    | exact resolve eq101 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (M.op X0 X1) X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq72
    | exact resolve eq72 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq132 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq133 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ X0)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq132
       have i₂ := eq99 sF3
       grind)
    | exact superpose eq99 eq132
    | exact resolve eq132 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq138 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq136
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq136
    | exact resolve eq136 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq148 : (σ (k y (k y (M.op x y)))) = (k (σ y) (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq133 eq36
    | exact resolve eq36 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq133
  have eq157 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq138
       grind)
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq171 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq168
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq168
    | exact resolve eq168 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq172 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq77 eq166
    | exact resolve eq166 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq166
  have eq174 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq171
       have i₂ := eq99 sF0
       grind)
    | exact superpose eq99 eq171
    | exact resolve eq171 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq175 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq172
    | exact resolve eq172 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq191 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq99 (τ X0)
       grind)
    | exact superpose eq99 eq34
    | exact resolve eq34 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq324 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq324
    | exact resolve eq324 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq338 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq337 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq337
    | exact resolve eq337 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq686 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq717 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq686 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq718 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq717 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq722 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq718 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq718
    | (have j0 := eq718 X0 X1
       grind)
    | exact resolve eq718 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq893 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq338 X0
       grind)
    | exact superpose eq338 eq16
    | exact resolve eq16 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq1311 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (M.op X0 X0)) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (τ X0) X2
       have i₂ := eq893 X0
       grind)
    | exact superpose eq893 eq14
    | exact resolve eq14 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq5280 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ X0)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq7799 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq715
    | (have j0 := eq715 X0 X1
       grind)
    | exact resolve eq715 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq7866 : (k (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7799 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq7799
    | (have j0 := eq7799 x y
       grind)
    | exact resolve eq7799 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7918 : (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7866
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq7866
    | exact resolve eq7866 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7866
  have eq7975 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7918
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7918
    | exact resolve eq7918 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7918
  have eq8029 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7975
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7975
    | exact resolve eq7975 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7975
  have eq8081 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq8029
    | exact resolve eq8029 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8029
  have eq8130 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8081
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8081
    | exact resolve eq8081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8081
  have eq8147 : (k (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8130
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8130
    | exact resolve eq8130 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8130
  have eq8158 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 X1
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq722
    | (have j0 := eq722 X0 X1
       grind)
    | exact resolve eq722 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq722
  have eq8159 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq8158 X0 X1
       have j1 := eq7799 X0 X1
       grind)
    | (have r₁ := eq8158 X0 X1
       have r₂ := eq7799 X0 X1
       grind)
    | exact resolve eq8158 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7799 eq8158
  have eq8166 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8159 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8159
    | exact resolve eq8159 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8225 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq8159 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8159
    | (have j0 := eq8159 x X0
       grind)
    | exact resolve eq8159 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8399 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) (σ X1)
       have i₂ := eq8159 X0 X1
       grind)
    | exact superpose eq8159 eq72
    | (have j1 := eq8159 X0 X1
       grind)
    | exact resolve eq72 eq8159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8159
  have eq8416 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8399 X0 X1
       have i₂ := eq10 X0 (k X0 X1)
       grind)
    | exact superpose eq10 eq8399
    | (have j0 := eq8399 X0 X1
       grind)
    | exact resolve eq8399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8399
  have eq8514 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8166 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq8166
    | (have j0 := eq8166 X0 X1
       grind)
    | exact resolve eq8166 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq8166
  have eq20095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq123 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq20095
    | exact resolve eq20095 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20095
  have eq20107 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq20096
       have r₂ := eq27
       grind)
    | exact resolve eq20096 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20096
  have eq20113 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq20107
    | exact resolve eq20107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20107
  have eq20115 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20113 eq96
    | (have r₁ := eq96
       have r₂ := eq20113
       grind)
    | exact resolve eq96 eq20113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq20113
  have eq20310 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq20115
  have eq20311 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq20310
  have eq20326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20311 eq123
    | exact resolve eq123 eq20311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20311
  have eq20336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq20326
  have eq20341 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq20336
       have r₂ := eq27
       grind)
    | exact resolve eq20336 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20336
  have eq20560 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20341 eq53
    | exact resolve eq53 eq20341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20566 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20341 eq107
    | exact resolve eq107 eq20341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20341
  have eq20584 : (M.op x y) = (M.op x x) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq20560
    | exact resolve eq20560 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20560
  have eq20585 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq94
       have i₂ := eq20584
       grind)
    | exact superpose eq20584 eq94
    | (have r₁ := eq94
       have r₂ := eq20584
       grind)
    | exact resolve eq94 eq20584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20586 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq20584
       grind)
    | exact superpose eq20584 eq103
    | exact resolve eq103 eq20584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq20584
  have eq20780 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y x) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20585
  have eq20781 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20780
  have eq20838 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq20586
    | exact resolve eq20586 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20586
  have eq20848 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20781
       grind)
    | exact superpose eq20781 eq44
    | exact resolve eq44 eq20781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20781
  have eq20870 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq20848
    | exact resolve eq20848 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20848
  have eq21513 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20566 eq123
    | exact resolve eq123 eq20566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq20566
  have eq21526 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq21513
  have eq21543 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y x) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq21526
       grind)
    | exact superpose eq21526 eq94
    | (have r₁ := eq94
       have r₂ := eq21526
       grind)
    | exact resolve eq94 eq21526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq21526
  have eq21738 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y x) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq21543
  have eq21739 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq21738
  have eq21807 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq21739
       grind)
    | exact superpose eq21739 eq44
    | exact resolve eq44 eq21739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21739
  have eq21829 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq21807
    | exact resolve eq21807 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21807
  have eq26091 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8225 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8225
    | (have j0 := eq8225 y
       grind)
    | exact resolve eq8225 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8225
  have eq26130 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26091
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq26091
    | exact resolve eq26091 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26091
  have eq26147 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq26130
    | exact resolve eq26130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26130
  have eq26482 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8514 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8514
    | exact resolve eq8514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8514
  have eq35522 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20870 eq8147
    | exact resolve eq8147 eq20870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8147 eq20870
  have eq35533 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq35522
       have r₂ := eq20838
       grind)
    | exact resolve eq35522 eq20838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20838 eq35522
  have eq35538 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq35533
       have r₂ := eq27
       grind)
    | exact resolve eq35533 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35533
  have eq35542 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35538 eq53
    | exact resolve eq53 eq35538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35538
  have eq35581 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq35542
    | exact resolve eq35542 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35542
  have eq35582 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq35581
  have eq35586 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq35582
       grind)
    | exact superpose eq35582 eq53
    | exact resolve eq53 eq35582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35590 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72 y x
       have i₂ := eq35582
       grind)
    | exact superpose eq35582 eq72
    | exact resolve eq72 eq35582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35593 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq107 y x
       have i₂ := eq35582
       grind)
    | exact superpose eq35582 eq107
    | exact resolve eq107 eq35582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq35582
  have eq35617 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35586
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35586
    | exact resolve eq35586 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35586
  have eq35624 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35617 eq70
    | exact resolve eq70 eq35617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq35617
  have eq36501 : (σ y) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8416 y x
       have i₂ := eq35590
       grind)
    | exact superpose eq35590 eq8416
    | (have j0 := eq8416 y x
       grind)
    | exact resolve eq8416 eq35590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8416
  have eq36506 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36501
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq36501
    | exact resolve eq36501 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36501
  have eq36519 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36506
       have i₂ := eq138
       grind)
    | exact superpose eq138 eq36506
    | exact resolve eq36506 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36506
  have eq36523 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36519
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36519
    | exact resolve eq36519 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36519
  have eq36525 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36523
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36523
    | exact resolve eq36523 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36523
  have eq36527 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36525
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36525
    | exact resolve eq36525 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36525
  have eq36529 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq36527
    | exact resolve eq36527 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36527
  have eq36530 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36529
  have eq36539 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq35593
       grind)
    | exact superpose eq35593 eq44
    | exact resolve eq44 eq35593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq35593
  have eq36577 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36539
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36539
    | exact resolve eq36539 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36539
  have eq36758 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35624 eq21829
    | exact resolve eq21829 eq35624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21829 eq35624
  have eq36767 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq36758
  have eq36860 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36530 eq63
    | exact resolve eq63 eq36530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq44964 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq36767
       grind)
    | exact superpose eq36767 eq53
    | exact resolve eq53 eq36767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36767
  have eq44996 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44964
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq44964
    | exact resolve eq44964 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44964
  have eq44997 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq44996
  have eq45298 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44997 eq28
    | exact resolve eq28 eq44997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq45317 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44997 eq175
    | exact resolve eq175 eq44997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq44997
  have eq45529 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45317
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq45317
    | exact resolve eq45317 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45317
  have eq45539 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq45298
    | exact resolve eq45298 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45298
  have eq45544 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45539 eq20
    | exact resolve eq20 eq45539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45561 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45539 eq174
    | exact resolve eq174 eq45539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq45742 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq45789 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45561
       have i₂ := eq138
       grind)
    | exact superpose eq138 eq45561
    | exact resolve eq45561 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45561
  have eq45800 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45544
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45544
    | exact resolve eq45544 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45544
  have eq46219 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45800 eq36530
    | exact resolve eq36530 eq45800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46226 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45800 eq36860
    | exact resolve eq36860 eq45800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36860
  have eq46240 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq46226
       have r₂ := eq27
       grind)
    | exact resolve eq46226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46226
  have eq46246 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq46219
       have r₂ := eq27
       grind)
    | exact resolve eq46219 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46219
  have eq47657 : ∀ X0 X1 : G, (M.op (M.op (τ (σ (M.op x y))) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq45529 eq1311
    | exact resolve eq1311 eq45529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311 eq45529
  have eq47830 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq30 eq47657
    | exact resolve eq47657 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47657
  have eq51229 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46246 eq191
    | exact resolve eq191 eq46246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq46246
  have eq51516 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq51229
    | exact resolve eq51229 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq51229
  have eq52503 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq45539 eq51516
    | exact resolve eq51516 eq45539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45539 eq51516
  have eq52810 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq52503
       have r₂ := eq45742
       grind)
    | exact resolve eq52503 eq45742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45742 eq52503
  have eq53122 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138
       have i₂ := eq52810
       grind)
    | exact superpose eq52810 eq138
    | exact resolve eq138 eq52810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq52810
  have eq53421 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53122
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq53122
    | exact resolve eq53122 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53122
  have eq59625 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45789 eq53421
    | exact resolve eq53421 eq45789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45789 eq53421
  have eq59856 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq59625
  have eq139977 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5280 x
       have i₂ := eq35590
       grind)
    | exact superpose eq35590 eq5280
    | (have j0 := eq5280 x
       grind)
    | exact resolve eq5280 eq35590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5280 eq35590
  have eq140047 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq139977
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq139977
    | exact resolve eq139977 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139977
  have eq140124 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq140047
       have r₂ := eq36530
       grind)
    | exact resolve eq140047 eq36530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36530 eq140047
  have eq140161 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140124
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140124
    | exact resolve eq140124 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140124
  have eq140187 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140161
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140161
    | exact resolve eq140161 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140161
  have eq140206 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq140187
    | exact resolve eq140187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140187
  have eq140207 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq140206
  have eq140219 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45800 eq140207
    | exact resolve eq140207 eq45800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140207
  have eq140564 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq140219
       have r₂ := eq27
       grind)
    | exact resolve eq140219 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140219
  have eq140820 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq140564 eq46240
    | exact resolve eq46240 eq140564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46240 eq140564
  have eq140873 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq140820
  have eq141504 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59856 eq140873
    | exact resolve eq140873 eq59856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59856 eq140873
  have eq141587 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq141504
  have eq141599 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq141587 eq53
    | exact resolve eq53 eq141587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141587
  have eq803841 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36577 eq26147
    | exact resolve eq26147 eq36577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26147 eq36577
  have eq804176 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq803841 eq53
    | exact resolve eq53 eq803841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803841
  have eq804319 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq804176
    | exact resolve eq804176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804176
  have eq804320 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq804319
  have eq804340 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq804320 eq27
    | exact resolve eq27 eq804320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804995 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45800 eq804340
    | (have r₁ := eq804340
       have r₂ := eq45800
       grind)
    | exact resolve eq804340 eq45800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804340
  have eq804996 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq804995
  have eq805344 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq804996 eq141599
    | exact resolve eq141599 eq804996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141599 eq804996
  have eq805697 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq805344
  have eq805764 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq805697
    | exact resolve eq805697 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805697
  have eq805778 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq805764 eq27
    | exact resolve eq27 eq805764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805764
  have eq806437 : x = (M.op x y) := by
    first
    | (have r₁ := eq805778
       have r₂ := eq45800
       grind)
    | exact resolve eq805778 eq45800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45800 eq805778
  have eq806443 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq806437 eq20
    | exact resolve eq20 eq806437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq807323 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq806443
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq806443
    | exact resolve eq806443 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806443
  have eq807332 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq807323 eq26
    | exact resolve eq26 eq807323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq807337 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq807323 eq55
    | exact resolve eq55 eq807323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq807341 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq807323 eq81
    | exact resolve eq81 eq807323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq810133 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq804320 eq807337
    | exact resolve eq807337 eq804320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807337
  have eq810236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq807323 eq810133
    | exact resolve eq810133 eq807323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810133
  have eq810237 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq810236
       have r₂ := eq27
       grind)
    | exact resolve eq810236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810236
  have eq810483 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq804320 eq807341
    | exact resolve eq807341 eq804320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804320 eq807341
  have eq810527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq807323 eq810483
    | exact resolve eq810483 eq807323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810483
  have eq810528 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq810527
       have r₂ := eq27
       grind)
    | exact resolve eq810527 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810527
  have eq812284 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq810237 eq53
    | exact resolve eq53 eq810237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq810237
  have eq812383 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq807332 eq812284
    | exact resolve eq812284 eq807332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807332 eq812284
  have eq812385 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq812383 eq27
    | exact resolve eq27 eq812383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq812383
  have eq821930 : (k (σ y) (k (σ y) (σ (M.op x y)))) = (σ (k y (M.op y (M.op x y)))) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq148
       have i₂ := eq26482 sF0 y
       grind)
    | exact superpose eq26482 eq148
    | (have j1 := eq26482 (M.op x y) y
       grind)
    | exact resolve eq148 eq26482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq26482
  have eq822890 : (σ y) = (k (σ y) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq821930
       have i₂ := eq72 y sF0
       grind)
    | exact superpose eq72 eq821930
    | exact resolve eq821930 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq821930
  have eq824355 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq810528 eq822890
    | exact resolve eq822890 eq810528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810528 eq822890
  have eq825410 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq824355
       have i₂ := eq99 sF3
       grind)
    | exact superpose eq99 eq824355
    | exact resolve eq824355 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq824355
  have eq826161 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq825410
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq825410
    | exact resolve eq825410 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825410
  have eq826705 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq806437 eq826161
    | exact resolve eq826161 eq806437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826161
  have eq827067 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq826705
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq826705
    | exact resolve eq826705 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826705
  have eq827283 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq806437 eq827067
    | exact resolve eq827067 eq806437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827067
  have eq828194 : (τ (σ y)) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq827283 eq157
    | exact resolve eq157 eq827283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq827283
  have eq829588 : y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq29 eq828194
    | exact resolve eq828194 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq828194
  have eq830902 : y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq47830 y y
       have i₂ := eq829588
       grind)
    | exact superpose eq829588 eq47830
    | exact resolve eq47830 eq829588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47830 eq829588
  have eq830923 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq806437 eq830902
    | exact resolve eq830902 eq806437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830902
  have eq831421 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq830923
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq830923
    | exact resolve eq830923 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830923
  have eq831719 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq806437 eq831421
    | exact resolve eq831421 eq806437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831421
  have eq831779 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq831719
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq831719
    | exact resolve eq831719 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq831719
  have eq831780 : y = (M.op x y) ∨ x = y := by grind
  clear eq831779
  have eq831809 : x = y ∨ x = y := by
    first
    | exact superpose eq806437 eq831780
    | exact resolve eq831780 eq806437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806437 eq831780
  have eq831810 : x = y := by grind
  clear eq831809
  have eq831814 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq831810
       grind)
    | exact superpose eq831810 eq24
    | exact resolve eq24 eq831810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq831810
  have eq832794 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq831814
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq831814
    | exact resolve eq831814 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq831814
  have eq832943 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq807323 eq832794
    | exact resolve eq832794 eq807323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807323 eq832794
  have eq833024 : False := by grind
  exact eq833024
