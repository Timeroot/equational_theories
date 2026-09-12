import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3089`: `x = (((x ◇ y) ◇ z) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_pyx_pxy_Equation3089 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3089 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3089.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X1) X0) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) y) x) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X1) X0 X1
       have i₂ := eq16 X0 X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq40
    | exact resolve eq40 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq41
    | exact resolve eq41 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq182
    | exact resolve eq182 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq184 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq181
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq181
    | exact resolve eq181 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq192 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq197 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq210 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X0 X1) X2
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq141
    | exact resolve eq141 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq266 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq245
    | exact resolve eq245 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq273 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq152
    | exact resolve eq152 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq294 : y = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq31 eq273
    | exact resolve eq273 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq745 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq179
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq179 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (k X0 X1) X2) X1) X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X2) X1) X0) = X0 ∨ (M.op (M.op (M.op (M.op X0 X1) X2) X1) (M.op (M.op (M.op X0 X1) X2) X1)) = X0 ∨ (M.op (M.op (M.op X0 X1) X2) X1) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 (M.op (M.op (M.op X0 X1) X2) X1) X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (M.op (M.op X0 X1) X2) X1) X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq770 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq771 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq197
       have i₂ := eq11 sF2 sF4
       grind)
    | exact superpose eq11 eq197
    | (have j1 := eq11 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq197 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq777 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq793 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq771
       have r₂ := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq771
       have r₂ := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq771 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq806 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X1) (M.op (M.op (M.op X0 X1) X2) X1)) = X0 ∨ (k (M.op (M.op (M.op X0 X1) X2) X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq748 X0 X1 X2
       have j1 := eq13 (M.op (M.op (M.op X0 X1) X2) X1) X0
       grind)
    | (have r₁ := eq748 (M.op X1 X1) X1 X2
       have r₂ := eq13 (k (M.op (M.op (M.op (M.op X1 X1) X1) X2) X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq748 X0 X1 X2
       have r₂ := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X1)
       grind)
    | (have r₁ := eq748 (M.op X1 X1) X1 X2
       have r₂ := eq13 (M.op (M.op (M.op (M.op (M.op X1 X1) X1) X2) X1) (M.op (M.op (M.op (M.op X1 X1) X1) X2) X1)) X1
       grind)
    | exact resolve eq748 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq825 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq778 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq778
    | (have j0 := eq778 (σ X0)
       grind)
    | exact resolve eq778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq829 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq793 eq90
    | exact resolve eq90 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq793
  have eq1436 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq762
       grind)
    | exact superpose eq762 eq40
    | exact resolve eq40 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1437 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1436
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1436
    | exact resolve eq1436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436
  have eq1439 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1437
    | exact resolve eq1437 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq3159 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq825 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq825
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq825 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3168 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3159 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3159
  have eq11383 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq806 (k X0 X1) X0 X1
       have i₂ := eq746 X0 X1 X0
       grind)
    | exact superpose eq746 eq806
    | (have j1 := eq746 X0 X1 x
       grind)
    | exact resolve eq806 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq11394 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X2) X1) X0) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X1)) ∨ (M.op (M.op (M.op X0 X1) X2) X1) = (M.op X0 X0) ∨ (k (M.op (M.op (M.op X0 X1) X2) X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq825 (M.op (M.op (M.op X0 X1) X2) X1)
       have i₂ := eq806 X0 X1 X2
       grind)
    | exact superpose eq806 eq825
    | (have j1 := eq806 X0 X1 X2
       grind)
    | exact resolve eq825 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq11407 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X2) X1) X0) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X1)) ∨ (k (M.op (M.op (M.op X0 X1) X2) X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq11394 X0 X1 X2
       have j1 := eq13 (M.op (M.op (M.op X0 X1) X2) X1) X0
       grind)
    | (have r₁ := eq11394 X1 X1 X2
       have r₂ := eq13 (M.op (M.op (M.op X1 X1) X2) X1) X1
       grind)
    | (have r₁ := eq11394 (M.op X1 X1) X1 X2
       have r₂ := eq13 (k (M.op (M.op (M.op (M.op X1 X1) X1) X2) X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq11394 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11394
  have eq16837 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1439 eq770
    | exact resolve eq770 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq16845 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16837
       have r₂ := eq27
       grind)
    | exact resolve eq16837 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16837
  have eq16852 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16845 eq266
    | exact resolve eq266 eq16845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16861 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16845 eq179
    | exact resolve eq179 eq16845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16845
  have eq16869 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq16861
    | exact resolve eq16861 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16861
  have eq16871 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq16852
    | exact resolve eq16852 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16852
  have eq16872 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16871
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq16871
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq16871
       have r₂ := eq13 x y
       grind)
    | exact resolve eq16871 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16871
  have eq16874 : y = (k (τ (σ x)) y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16872 eq294
    | exact resolve eq294 eq16872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16872
  have eq16892 : y = (k x y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq16874
    | exact resolve eq16874 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16874
  have eq16894 : y = (k x y) ∨ x = (k y x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq16892
       have r₂ := eq13 x y
       grind)
    | exact resolve eq16892 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16892
  have eq16898 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq762
       have i₂ := eq16894
       grind)
    | exact superpose eq16894 eq762
    | exact resolve eq762 eq16894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16905 : x = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16898
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq16898
       have r₂ := eq13 x y
       grind)
    | exact resolve eq16898 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16898
  have eq17104 : y = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16869 eq294
    | exact resolve eq294 eq16869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq16869
  have eq17122 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq17104
    | exact resolve eq17104 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17104
  have eq17124 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq17122
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq17122
       have r₂ := eq13 x y
       grind)
    | exact resolve eq17122 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17122
  have eq17128 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq762
       have i₂ := eq17124
       grind)
    | exact superpose eq17124 eq762
    | exact resolve eq762 eq17124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17129 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq17124
       grind)
    | exact superpose eq17124 eq35
    | exact resolve eq35 eq17124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq17124
  have eq17133 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17128
  have eq17136 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17129
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17129
    | exact resolve eq17129 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17129
  have eq17145 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17136 eq770
    | exact resolve eq770 eq17136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17136
  have eq17151 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq17145
  have eq17171 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq17133
       grind)
    | exact superpose eq17133 eq179
    | exact resolve eq179 eq17133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17133
  have eq17179 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17171
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17171
    | exact resolve eq17171 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17171
  have eq17180 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17179
  have eq17184 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184
       have i₂ := eq17180
       grind)
    | exact superpose eq17180 eq184
    | exact resolve eq184 eq17180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq17185 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq825 y
       have i₂ := eq17180
       grind)
    | exact superpose eq17180 eq825
    | exact resolve eq825 eq17180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17180
  have eq17201 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17185
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17185
    | exact resolve eq17185 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17185
  have eq17202 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17184
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17184
    | exact resolve eq17184 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17184
  have eq17237 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17202 eq770
    | exact resolve eq770 eq17202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17202
  have eq17242 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17237
  have eq17526 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq17201
       grind)
    | exact superpose eq17201 eq39
    | exact resolve eq39 eq17201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17201
  have eq17531 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17526
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17526
    | exact resolve eq17526 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17526
  have eq17535 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17531
    | exact resolve eq17531 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17531
  have eq17569 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17242 eq179
    | exact resolve eq179 eq17242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17242
  have eq17577 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17569
    | exact resolve eq17569 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17569
  have eq17578 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17577
  have eq17583 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17578 eq825
    | exact resolve eq825 eq17578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17578
  have eq17599 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17583
    | exact resolve eq17583 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17583
  have eq17705 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq745 y x
       have i₂ := eq16905
       grind)
    | exact superpose eq16905 eq745
    | (have j0 := eq745 y x
       grind)
    | exact resolve eq745 eq16905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16905
  have eq17751 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq17705
  have eq18114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17599 eq17535
    | exact resolve eq17535 eq17599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17535 eq17599
  have eq18123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq18114
  have eq18130 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq18123
       have r₂ := eq27
       grind)
    | exact resolve eq18123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123
  have eq18168 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18130 eq179
    | exact resolve eq179 eq18130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18130
  have eq18178 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq18168
    | exact resolve eq18168 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18168
  have eq18179 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18178
  have eq18199 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq18179
       grind)
    | exact superpose eq18179 eq179
    | exact resolve eq179 eq18179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18179
  have eq18209 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18199
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18199
    | exact resolve eq18199 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18199
  have eq18210 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18209
  have eq18216 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18210 eq27
    | exact resolve eq27 eq18210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18222 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18210 eq829
    | exact resolve eq829 eq18210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq18223 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq18222
    | exact resolve eq18222 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18222
  have eq18310 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18223 eq11
    | exact resolve eq11 eq18223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18223
  have eq18319 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq18310
  have eq18547 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18319 eq97
    | exact resolve eq97 eq18319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq18319
  have eq18562 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq18547
    | exact resolve eq18547 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18547
  have eq18570 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq762
       have i₂ := eq18562
       grind)
    | exact superpose eq18562 eq762
    | exact resolve eq762 eq18562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq18562
  have eq18575 : y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq18570
  have eq18816 : x = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17151 eq266
    | exact resolve eq266 eq17151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18829 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17151 eq179
    | exact resolve eq179 eq17151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17151
  have eq18845 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq18829
    | exact resolve eq18829 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18829
  have eq18846 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq18845
  have eq18856 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq18816
    | exact resolve eq18816 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18816
  have eq18858 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18210 eq18846
    | exact resolve eq18846 eq18210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18846
  have eq18860 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq18856
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq18856
       have r₂ := eq13 y x
       grind)
    | exact resolve eq18856 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18856
  have eq18861 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq18210 eq18860
    | exact resolve eq18860 eq18210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18860
  have eq18862 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq18858
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq18858
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq18858 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18866 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18858 eq825
    | exact resolve eq825 eq18858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18870 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18858 eq11
    | (have j0 := eq11 x (M.op x y)
       grind)
    | exact resolve eq11 eq18858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18871 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq18858 eq16
    | exact resolve eq16 eq18858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18874 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18858 eq179
    | exact resolve eq179 eq18858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18858
  have eq18879 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq18870
  have eq18880 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq18862
  have eq18882 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq18866
    | exact resolve eq18866 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18866
  have eq18884 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18879 eq18880
    | exact resolve eq18880 eq18879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18880
  have eq18899 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq18861 eq210
    | exact resolve eq210 eq18861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18861
  have eq19016 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18879 eq115
    | exact resolve eq115 eq18879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18879
  have eq19035 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq29 eq19016
    | exact resolve eq19016 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19016
  have eq19040 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18210 eq19035
    | exact resolve eq19035 eq18210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19035
  have eq19447 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq197 eq18871
    | (have j0 := eq18871 (σ y)
       grind)
    | exact resolve eq18871 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19500 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq19447 eq210
    | exact resolve eq210 eq19447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19447
  have eq19674 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq197 eq18899
    | (have j0 := eq18899 (σ y)
       grind)
    | exact resolve eq18899 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq19750 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq19500 eq210
    | exact resolve eq210 eq19500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19500
  have eq20034 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq17751
       grind)
    | exact superpose eq17751 eq179
    | exact resolve eq179 eq17751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17751
  have eq20047 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20034
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20034
    | exact resolve eq20034 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20034
  have eq20048 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq20047
  have eq20533 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18882 eq114
    | exact resolve eq114 eq18882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq18882
  have eq20562 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18210 eq20533
    | exact resolve eq20533 eq18210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20533
  have eq20566 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18884 eq115
    | exact resolve eq115 eq18884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq18884
  have eq20587 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29 eq20566
    | exact resolve eq20566 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20566
  have eq20592 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18210 eq20587
    | exact resolve eq20587 eq18210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20587
  have eq20682 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20592 eq18871
    | exact resolve eq18871 eq20592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18871 eq20592
  have eq20702 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq20682
  have eq20719 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq20702
    | exact resolve eq20702 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20702
  have eq20726 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq19040 eq20719
    | exact resolve eq20719 eq19040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19040 eq20719
  have eq20878 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20726 eq19674
    | exact resolve eq19674 eq20726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19674 eq20726
  have eq20895 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq20878
  have eq20910 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq20895
       have r₂ := eq13 (M.op x y) x
       grind)
    | exact resolve eq20895 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20895
  have eq20917 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq20910
    | exact resolve eq20910 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20910
  have eq20918 : x = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20917
  have eq20973 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20918 eq41
    | exact resolve eq41 eq20918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq20987 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq20973
    | exact resolve eq20973 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20973
  have eq20994 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20987
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20987
    | exact resolve eq20987 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20987
  have eq22295 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20918 eq3168
    | (have j0 := eq3168 (M.op x y)
       grind)
    | exact resolve eq3168 eq20918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20918
  have eq22348 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq22295
       have r₂ := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq22295
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq22295 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22295
  have eq22354 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq192 eq22348
    | exact resolve eq22348 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22348
  have eq22362 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22354 eq39
    | exact resolve eq39 eq22354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22354
  have eq22371 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22362
    | exact resolve eq22362 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22362
  have eq23359 : (k (σ (M.op x y)) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20562 eq39
    | exact resolve eq39 eq20562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20562
  have eq23377 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq23359
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq23359
    | exact resolve eq23359 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23359
  have eq23383 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq23377
    | exact resolve eq23377 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23377
  have eq23400 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq23383 eq22371
    | exact resolve eq22371 eq23383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22371
  have eq23411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq23400
  have eq23426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq23411
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq23411
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq23411
       have r₂ := eq13 (M.op x y) x
       grind)
    | exact resolve eq23411 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23411
  have eq23428 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq23426
       have r₂ := eq27
       grind)
    | exact resolve eq23426 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23426
  have eq23462 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq23428 eq179
    | exact resolve eq179 eq23428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23428
  have eq23484 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq23462
    | exact resolve eq23462 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23462
  have eq23485 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23484
  have eq23498 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23485 eq183
    | exact resolve eq183 eq23485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq23510 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23485 eq174
    | exact resolve eq174 eq23485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23485
  have eq23530 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23498
    | exact resolve eq23498 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23498
  have eq23536 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20994 eq23530
    | exact resolve eq23530 eq20994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20994 eq23530
  have eq23598 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23510 eq827
    | (have j0 := eq827 (M.op x y)
       grind)
    | exact resolve eq827 eq23510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23510
  have eq23606 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23598
  have eq23616 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23606
    | exact resolve eq23606 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23606
  have eq23623 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23536 eq23616
    | exact resolve eq23616 eq23536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23536 eq23616
  have eq23697 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23623 eq18899
    | exact resolve eq18899 eq23623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18899
  have eq23712 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq23697
  have eq23731 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq23623 eq23712
    | exact resolve eq23712 eq23623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23623 eq23712
  have eq23741 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq23731
    | exact resolve eq23731 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23731
  have eq23742 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23741
  have eq23753 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23742 eq37
    | exact resolve eq37 eq23742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq23742
  have eq23761 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23753
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23753
    | exact resolve eq23753 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23753
  have eq23772 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23761 eq23383
    | exact resolve eq23383 eq23761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23383 eq23761
  have eq23777 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq23772
  have eq23911 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq23777 eq179
    | exact resolve eq179 eq23777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23777
  have eq23935 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq23911
    | exact resolve eq23911 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23911
  have eq23936 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23935
  have eq25407 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq19750 eq210
    | exact resolve eq210 eq19750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19750
  have eq25430 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq23936 eq25407
    | exact resolve eq25407 eq23936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25407
  have eq25447 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq25430
    | exact resolve eq25430 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25430
  have eq25461 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (M.op (σ y) (σ x)))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq23936 eq25447
    | exact resolve eq25447 eq23936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23936 eq25447
  have eq25474 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ x))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18874 eq25461
    | exact resolve eq25461 eq18874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25461
  have eq25532 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq25474 eq16
    | exact resolve eq16 eq25474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25474
  have eq25557 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq25532
       have i₂ := eq179 sF2 sF2
       grind)
    | exact superpose eq179 eq25532
    | exact resolve eq25532 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25532
  have eq25591 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq25557 eq16
    | exact resolve eq16 eq25557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25621 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18874 eq25591
    | exact resolve eq25591 eq18874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18874 eq25591
  have eq25707 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq25621 eq25557
    | exact resolve eq25557 eq25621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25557 eq25621
  have eq25741 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq25707
  have eq25765 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq25741
    | exact resolve eq25741 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25741
  have eq25766 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25765
  have eq25797 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq25766
       grind)
    | exact superpose eq25766 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq25766
       grind)
    | exact resolve eq13 eq25766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25803 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq25766
       grind)
    | exact superpose eq25766 eq11
    | exact resolve eq11 eq25766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25766
  have eq25812 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25803
  have eq25842 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq25812
       grind)
    | exact superpose eq25812 eq39
    | exact resolve eq39 eq25812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25864 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25842
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25842
    | exact resolve eq25842 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25842
  have eq25870 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq25864
    | exact resolve eq25864 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25864
  have eq25902 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25870 eq745
    | (have j0 := eq745 (σ x) (σ x)
       grind)
    | exact resolve eq745 eq25870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25870
  have eq25905 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25902
  have eq26552 : x = (k (τ (σ x)) x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25905 eq266
    | exact resolve eq266 eq25905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq25905
  have eq26625 : x = (k x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq26552
    | exact resolve eq26552 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26552
  have eq26633 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq25797 x
       grind)
    | (have r₁ := eq26625
       have r₂ := eq25797 x
       grind)
    | exact resolve eq26625 eq25797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26625
  have eq50377 : (k x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3168 x
       have i₂ := eq18575
       grind)
    | exact superpose eq18575 eq3168
    | (have j0 := eq3168 x
       grind)
    | exact resolve eq3168 eq18575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168
  have eq50383 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq745 x x
       have i₂ := eq18575
       grind)
    | exact superpose eq18575 eq745
    | (have j0 := eq745 x x
       grind)
    | exact resolve eq745 eq18575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50386 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq50383
  have eq50391 : (k x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq50377
  have eq50429 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50386
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50386
    | exact resolve eq50386 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50386
  have eq50430 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq50429
  have eq50435 : (k x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq50391
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq50391
       have r₂ := eq12 x x
       grind)
    | (have r₁ := eq50391
       have r₂ := eq12 x y
       grind)
    | exact resolve eq50391 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50391
  have eq50455 : x = (k x y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20048 eq50435
    | exact resolve eq50435 eq20048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20048 eq50435
  have eq51727 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq50430
       grind)
    | exact superpose eq50430 eq179
    | exact resolve eq179 eq50430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50430
  have eq51803 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51727
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51727
    | exact resolve eq51727 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51727
  have eq51804 : x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq51803
  have eq52705 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11383 x y
       have i₂ := eq50455
       grind)
    | exact superpose eq50455 eq11383
    | (have j0 := eq11383 x x
       grind)
    | exact resolve eq11383 eq50455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11383 eq50455
  have eq52710 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq52705
  have eq52726 : x = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq52710
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq52710
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq52710
       have r₂ := eq13 x y
       grind)
    | exact resolve eq52710 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52710
  have eq52728 : x = (k x x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51804 eq52726
    | exact resolve eq52726 eq51804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52726
  have eq52762 : x = y ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18575
       have i₂ := eq52728
       grind)
    | exact superpose eq52728 eq18575
    | exact resolve eq18575 eq52728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18575 eq52728
  have eq52816 : x = y ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq52762
  have eq52850 : x = y ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51804 eq52816
    | exact resolve eq52816 eq51804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51804 eq52816
  have eq52851 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq52850
  have eq52875 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq825 y
       have i₂ := eq52851
       grind)
    | exact superpose eq52851 eq825
    | exact resolve eq825 eq52851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq52882 : x = (k y y) ∨ x = y ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq52851
       grind)
    | exact superpose eq52851 eq11
    | exact resolve eq11 eq52851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52883 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq52851
       grind)
    | exact superpose eq52851 eq16
    | exact resolve eq16 eq52851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52851
  have eq52904 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq52882
  have eq52922 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52875
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52875
    | exact resolve eq52875 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52875
  have eq52959 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq52904
       grind)
    | exact superpose eq52904 eq40
    | exact resolve eq40 eq52904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq52904
  have eq52986 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52959
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq52959
    | exact resolve eq52959 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52959
  have eq52994 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52986
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52986
    | exact resolve eq52986 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52986
  have eq53045 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52994 eq745
    | (have j0 := eq745 (σ y) (σ y)
       grind)
    | exact resolve eq745 eq52994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq53048 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq53045
  have eq53066 : y = (M.op (M.op (M.op x y) y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq192 eq52883
    | (have j0 := eq52883 y
       grind)
    | exact resolve eq52883 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq52883
  have eq53589 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq52922
       grind)
    | exact superpose eq52922 eq39
    | exact resolve eq39 eq52922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq52922
  have eq53608 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53589
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq53589
    | exact resolve eq53589 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53589
  have eq53614 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq53608
    | exact resolve eq53608 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53608
  have eq53733 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53048 eq174
    | exact resolve eq174 eq53048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq53048
  have eq53798 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52994 eq53733
    | exact resolve eq53733 eq52994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52994 eq53733
  have eq53799 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq53798
  have eq53851 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq53799 eq210
    | exact resolve eq210 eq53799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq53799
  have eq53967 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq53851 eq11407
    | exact resolve eq11407 eq53851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11407 eq53851
  have eq54025 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq53967
    | exact resolve eq53967 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53967
  have eq54036 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18210 eq54025
    | exact resolve eq54025 eq18210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54025
  have eq55537 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53614 eq54036
    | exact resolve eq54036 eq53614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53614 eq54036
  have eq55589 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq55537
  have eq55605 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq55589
       have r₂ := eq18216
       grind)
    | exact resolve eq55589 eq18216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55589
  have eq55676 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq55605
       grind)
    | exact superpose eq55605 eq179
    | exact resolve eq179 eq55605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq55605
  have eq55745 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq55676
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55676
    | exact resolve eq55676 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55676
  have eq55746 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq55745
  have eq55774 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq55746 eq31
    | exact resolve eq31 eq55746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq55746
  have eq56216 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq55774
    | exact resolve eq55774 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55774
  have eq56217 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq56216
  have eq56268 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56217 eq28
    | exact resolve eq28 eq56217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq56322 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56217 eq18216
    | exact resolve eq18216 eq56217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18216 eq56217
  have eq56412 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq56322
  have eq56473 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq56268
    | exact resolve eq56268 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq56268
  have eq56503 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq56473
       grind)
    | exact superpose eq56473 eq24
    | exact resolve eq24 eq56473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56473
  have eq56562 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq56503
    | exact resolve eq56503 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56503
  have eq56670 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56562 eq26633
    | exact resolve eq26633 eq56562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26633
  have eq56758 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have j1 := eq25797 x
       grind)
    | (have r₁ := eq56670
       have r₂ := eq25797 x
       grind)
    | exact resolve eq56670 eq25797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56670
  have eq56887 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq56758
    | exact resolve eq56758 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56758
  have eq56888 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = y := by grind
  clear eq56887
  have eq56901 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18210 eq56888
    | exact resolve eq56888 eq18210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18210 eq56888
  have eq56904 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq25797 x
       grind)
    | (have r₁ := eq56901
       have r₂ := eq25797 x
       grind)
    | exact resolve eq56901 eq25797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25797 eq56901
  have eq56953 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25812
       have i₂ := eq56904
       grind)
    | exact superpose eq56904 eq25812
    | exact resolve eq25812 eq56904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25812
  have eq56962 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq827 x
       have i₂ := eq56904
       grind)
    | exact superpose eq56904 eq827
    | (have j0 := eq827 x
       grind)
    | exact resolve eq827 eq56904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq56904
  have eq56979 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq56962
  have eq56983 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq56953
  have eq57035 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56979
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56979
    | exact resolve eq56979 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56979
  have eq57055 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56983 eq27
    | exact resolve eq27 eq56983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56983
  have eq57097 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56562 eq57055
    | (have r₁ := eq57055
       have r₂ := eq56562
       grind)
    | exact resolve eq57055 eq56562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56562 eq57055
  have eq57099 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq57097
  have eq57100 : x = (M.op x y) ∨ x = y := by grind
  clear eq57099
  have eq57101 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq57100
       grind)
    | exact superpose eq57100 eq18
    | exact resolve eq18 eq57100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58022 : y = (M.op (M.op x y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq57101 eq53066
    | exact resolve eq53066 eq57101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53066
  have eq58080 : y = (M.op (M.op x y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq58022
  have eq58119 : y = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq58080
       have r₂ := eq56412
       grind)
    | exact resolve eq58080 eq56412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56412 eq58080
  have eq58144 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq57101 eq58119
    | exact resolve eq58119 eq57101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57101 eq58119
  have eq58145 : y = (M.op x y) ∨ x = y := by grind
  clear eq58144
  have eq58209 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq58145
  have eq58211 : x = y := by
    first
    | (have r₁ := eq58209
       have r₂ := eq57100
       grind)
    | exact resolve eq58209 eq57100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57100 eq58209
  have eq58235 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq58211
       grind)
    | exact superpose eq58211 eq18
    | exact resolve eq18 eq58211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq58236 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq58211
       grind)
    | exact superpose eq58211 eq24
    | exact resolve eq24 eq58211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq58271 : x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16894
       have i₂ := eq58211
       grind)
    | exact superpose eq58211 eq16894
    | exact resolve eq16894 eq58211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16894 eq58211
  have eq58369 : x = (k x x) := by grind
  clear eq58271
  have eq58399 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq58236
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq58236
    | exact resolve eq58236 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58236
  have eq58401 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq58399 eq26
    | exact resolve eq26 eq58399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq58454 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq58399 eq770
    | exact resolve eq770 eq58399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq58637 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq58454
  have eq58766 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq57035 eq58637
    | exact resolve eq58637 eq57035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57035 eq58637
  have eq58884 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq58399 eq58766
    | exact resolve eq58766 eq58399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58399 eq58766
  have eq58930 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq58884
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq58884 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58884
  have eq59031 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq58235
       grind)
    | exact superpose eq58235 eq11
    | exact resolve eq11 eq58235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58235
  have eq59053 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq59031
  have eq59065 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59053
       have i₂ := eq58369
       grind)
    | exact superpose eq58369 eq59053
    | exact resolve eq59053 eq58369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58369 eq59053
  have eq59066 : x = (M.op x y) := by grind
  clear eq59065
  have eq59079 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq59066
       grind)
    | exact superpose eq59066 eq22
    | exact resolve eq22 eq59066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq59066
  have eq59601 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq59079 eq20
    | exact resolve eq20 eq59079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq59079
  have eq60763 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58401 eq11
    | exact resolve eq11 eq58401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58401
  have eq60785 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60763
  have eq60813 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58930 eq60785
    | exact resolve eq60785 eq58930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58930 eq60785
  have eq60814 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60813
  have eq60830 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq60814 eq27
    | exact resolve eq27 eq60814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq60814
  have eq60902 : False := by grind
  exact eq60902

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_y_pyx_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq57
    | (have j0 := eq57 (σ X0) (σ X1)
       grind)
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq22
    | exact resolve eq22 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq89 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq90 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq91 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq88
    | exact resolve eq88 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq90
    | exact resolve eq90 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq91
    | exact resolve eq91 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq91
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq135 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 y x
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 y x
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq497 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq135
    | (have j1 := eq57 (σ y) (σ x)
       grind)
    | exact resolve eq135 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq135
  have eq498 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq497
  have eq582 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) (σ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq81
    | exact resolve eq81 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq653 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25 x y
       have i₂ := eq498
       grind)
    | exact superpose eq498 eq25
    | exact resolve eq25 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq1104 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq81 (σ x) (σ y) X0
       have i₂ := eq653
       grind)
    | exact superpose eq653 eq81
    | exact resolve eq81 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq1108 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1104 X0
       have i₂ := eq25 (σ x) X0
       grind)
    | exact superpose eq25 eq1104
    | exact resolve eq1104 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1244 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 x x X0
       have i₂ := eq1108 X1
       grind)
    | exact superpose eq1108 eq81
    | (have j1 := eq1108 X1
       grind)
    | exact resolve eq81 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1252 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1244 X0 X1
       have i₂ := eq25 x X0
       grind)
    | exact superpose eq25 eq1244
    | (have j0 := eq1244 X0 X1
       grind)
    | exact resolve eq1244 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1370 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq25 x X0
       have i₂ := eq1252 X0 X1
       grind)
    | exact superpose eq1252 eq25
    | (have j1 := eq1252 X0 X1
       grind)
    | exact resolve eq25 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1439 : ∀ X0 : G, (M.op x x) = (τ (σ x)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq99 x
       have i₂ := eq1370 X0 (σ x)
       grind)
    | exact superpose eq1370 eq99
    | (have j1 := eq1370 X0 x
       grind)
    | exact resolve eq99 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1370
  have eq1482 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1439 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1439
    | (have j0 := eq1439 x
       grind)
    | exact resolve eq1439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1679 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq1482 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq1680 : x = (M.op x x) := by grind
  clear eq1679
  have eq1883 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq582 x X0
       have i₂ := eq1680
       grind)
    | exact superpose eq1680 eq582
    | exact resolve eq582 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq1894 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq81 x x X0
       have i₂ := eq1680
       grind)
    | exact superpose eq1680 eq81
    | exact resolve eq81 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq1680
  have eq1909 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1894 X0
       have i₂ := eq25 x X0
       grind)
    | exact superpose eq25 eq1894
    | exact resolve eq1894 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq1916 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1883 X0
       have i₂ := eq25 (σ x) X0
       grind)
    | exact superpose eq25 eq1883
    | exact resolve eq1883 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1883
  have eq2929 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1916 (σ y)
       grind)
    | exact superpose eq1916 eq16
    | exact resolve eq16 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916
  have eq2994 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2929
       have i₂ := eq1909 y
       grind)
    | exact superpose eq1909 eq2929
    | exact resolve eq2929 eq1909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909 eq2929
  have eq2995 : False := by grind
  exact eq2995

/-- `Equation3197`: `x = (((y ◇ z) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_x_pyx_pxx_pyx_Equation3197 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3197 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3197.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op X0 X0) X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
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
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq86
    | exact resolve eq86 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq86
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
  have eq139 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq165 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq9
    | exact resolve eq9 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (M.op (M.op (M.op X0 X1) X0) X0)) (σ (M.op (M.op (M.op X0 X1) X0) X0))) (σ (M.op (M.op (M.op X0 X1) X0) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165 (M.op (M.op (M.op X0 X1) X0) X0) X2
       have i₂ := eq9 (M.op (M.op (M.op X0 X1) X0) X0) X0 X1
       grind)
    | exact superpose eq9 eq165
    | exact resolve eq165 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op (M.op (M.op (M.op X0 X1) X0) X0) (M.op (M.op (M.op X0 X1) X0) X0))) (σ (M.op (M.op (M.op X0 X1) X0) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq328 X0 X1 X2
       have i₂ := eq98 (M.op (M.op (M.op X0 X1) X0) X0)
       grind)
    | exact superpose eq98 eq328
    | exact resolve eq328 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq377 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op (M.op (M.op X0 X1) X0) X0)) (σ (M.op (M.op (M.op X0 X1) X0) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq369 X0 X1 X2
       have i₂ := eq9 (M.op (M.op (M.op X0 X1) X0) X0) X0 X1
       grind)
    | exact superpose eq9 eq369
    | exact resolve eq369 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq381 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op (M.op (M.op X0 X1) X0) X0) (M.op (M.op (M.op X0 X1) X0) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq377 X0 X1 X2
       have i₂ := eq98 (M.op (M.op (M.op X0 X1) X0) X0)
       grind)
    | exact superpose eq98 eq377
    | exact resolve eq377 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq385 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op (M.op X0 X1) X0) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq381 X0 X1 X2
       have i₂ := eq9 (M.op (M.op (M.op X0 X1) X0) X0) X0 X1
       grind)
    | exact superpose eq9 eq381
    | exact resolve eq381 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq664 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq139
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq139
    | (have j1 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq139 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq139
  have eq667 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq664
  have eq668 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (M.op (M.op y y) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq667
       grind)
    | exact superpose eq667 eq9
    | exact resolve eq9 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0))) (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)))) (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208 (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) X1
       have i₂ := eq165 X0 (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0))
       grind)
    | exact superpose eq165 eq208
    | exact resolve eq208 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq794 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)))) (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq744 X0 X1
       have i₂ := eq105 (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0))
       grind)
    | exact superpose eq105 eq744
    | exact resolve eq744 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq806 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0))) (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq794 X0 X1
       have i₂ := eq165 X0 (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0))
       grind)
    | exact superpose eq165 eq794
    | exact resolve eq794 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq815 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X1
       have i₂ := eq105 (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0))
       grind)
    | exact superpose eq105 eq806
    | exact resolve eq806 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq806
  have eq823 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq815 X0 X1
       have i₂ := eq165 X0 (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0))
       grind)
    | exact superpose eq165 eq815
    | exact resolve eq815 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq815
  have eq12170 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ y)) X0) = X0 ∨ (M.op (M.op (M.op y y) y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq668 X1
       grind)
    | exact superpose eq668 eq9
    | (have j1 := eq668 X1
       grind)
    | exact resolve eq9 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq12264 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op y y)) (σ y)) X0) = X0 ∨ (M.op (M.op (M.op y y) y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12170 X0 X1
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq12170
    | (have j0 := eq12170 X0 X1
       grind)
    | exact resolve eq12170 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12170
  have eq359956 : ∀ X0 X1 : G, (M.op (τ (σ y)) X0) = X0 ∨ (M.op (M.op (M.op y y) y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq823 y X0
       have i₂ := eq12264 (σ y) X1
       grind)
    | exact superpose eq12264 eq823
    | (have j1 := eq12264 X0 X1
       grind)
    | exact resolve eq823 eq12264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823 eq12264
  have eq360745 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op (M.op (M.op y y) y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq359956 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq359956
    | (have j0 := eq359956 X0 X1
       grind)
    | exact resolve eq359956 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359956
  have eq362439 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op y y) y) X2) = X2 ∨ (M.op (M.op (M.op X0 y) y) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 y X0
       have i₂ := eq360745 X0 X2
       grind)
    | exact superpose eq360745 eq9
    | (have j1 := eq360745 X0 X2
       grind)
    | exact resolve eq9 eq360745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360745
  have eq384252 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op y y) y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq362439 y X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362439
  have eq384253 : ∀ X0 : G, (M.op (M.op (M.op y y) y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq384252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384252
  have eq386364 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq384253 y
       grind)
    | exact superpose eq384253 eq9
    | exact resolve eq9 eq384253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386387 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq385 y y X0
       have i₂ := eq384253 y
       grind)
    | exact superpose eq384253 eq385
    | exact resolve eq385 eq384253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq384253
  have eq389378 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq386364 x
       have i₂ := eq667
       grind)
    | exact superpose eq667 eq386364
    | exact resolve eq386364 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq386364
  have eq584083 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq389378
       have i₂ := eq386387 (σ x)
       grind)
    | exact superpose eq386387 eq389378
    | exact resolve eq389378 eq386387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386387 eq389378
  have eq585278 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq584083
       grind)
    | exact superpose eq584083 eq16
    | exact resolve eq16 eq584083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584083
  have eq585344 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq585278
       have r₂ := eq98 x
       grind)
    | exact resolve eq585278 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585278
  have eq586415 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq585344
       grind)
    | exact superpose eq585344 eq10
    | exact resolve eq10 eq585344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585344
  have eq586869 : x = y := by
    first
    | (have i₁ := eq586415
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq586415
    | exact resolve eq586415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586415
  have eq588803 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq586869
       grind)
    | exact superpose eq586869 eq16
    | exact resolve eq16 eq586869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586869
  have eq588869 : False := by grind
  exact eq588869

/-- `Equation3197`: `x = (((y ◇ z) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_pxy_pyx_pxy_Equation3197 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3197 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3197.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X1)) (M.op (M.op (M.op X1 X2) X1) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X2) X1) X1) X0
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X0) ≠ (M.op (M.op (M.op X0 X1) X0) X0) ∨ (M.op (M.op (M.op (M.op X0 X1) X0) X0) X2) = (k (M.op (M.op (M.op X0 X1) X0) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X0 X1) X0) X0) X2
       have i₂ := eq9 (M.op (M.op (M.op X0 X1) X0) X0) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X0 X1) X0) X0) X2
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X1 X2) X1) X1) X1
       have r₂ := eq9 (M.op (M.op (M.op X1 X2) X1) X1) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X0) X2) = (k (M.op (M.op (M.op X0 X1) X0) X0) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X0) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq69 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op (M.op (M.op X1 X2) X1) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op (M.op X1 X2) X1) X1)
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op (M.op (M.op X1 X2) X1) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op (M.op (M.op X1 X2) X1) X1) X0
       have i₂ := eq35 X1 X2 (σ X0)
       grind)
    | exact superpose eq35 eq24
    | exact resolve eq24 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X1 X2) X1) X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op (M.op X1 X2) X1) X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq102 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (τ (M.op (M.op (M.op X1 X2) X1) X1)) X0
       have i₂ := eq71 (σ X0) X1 X2
       grind)
    | exact superpose eq71 eq24
    | exact resolve eq24 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 X2 : G, (k (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq146 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))) X0
       have i₂ := eq104 (σ X0) X1 X2
       grind)
    | exact superpose eq104 eq24
    | exact resolve eq24 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 : G, (k (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1)))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq146
    | exact resolve eq146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq220 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1)))) X0
       have i₂ := eq148 (σ X0) X1 X2
       grind)
    | exact superpose eq148 eq24
    | exact resolve eq24 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq222 : ∀ X0 X1 X2 : G, (k (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq220
    | exact resolve eq220 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq226 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq79
    | exact resolve eq79 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq247 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq243 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq249 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq247 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq247 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq247 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq545 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (M.op X0 X1) X0) X0)) ≠ (σ (M.op (M.op (M.op X0 X1) X0) X0)) ∨ (k (σ (M.op (M.op (M.op X0 X1) X0) X0)) X2) = (M.op (σ (M.op (M.op (M.op X0 X1) X0) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq249 (M.op (M.op (M.op X0 X1) X0) X0) X2
       have i₂ := eq35 X0 X1 (M.op (M.op (M.op X0 X1) X0) X0)
       grind)
    | exact superpose eq35 eq249
    | (have j0 := eq249 (M.op (M.op (M.op X0 X1) X0) X0) X2
       grind)
    | exact resolve eq249 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 : G, (σ (τ (τ (M.op (M.op (M.op X0 X1) X0) X0)))) ≠ (σ (τ (τ (M.op (M.op (M.op X0 X1) X0) X0)))) ∨ (k (σ (τ (τ (M.op (M.op (M.op X0 X1) X0) X0)))) X2) = (M.op (σ (τ (τ (M.op (M.op (M.op X0 X1) X0) X0)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq249 (τ (τ (M.op (M.op (M.op X0 X1) X0) X0))) X2
       have i₂ := eq104 (τ (τ (M.op (M.op (M.op X0 X1) X0) X0))) X0 X1
       grind)
    | exact superpose eq104 eq249
    | (have j0 := eq249 (τ (τ (M.op (M.op (M.op X0 X1) X0) X0))) X2
       grind)
    | exact resolve eq249 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq249
  have eq558 : ∀ X0 X1 X2 : G, (k (σ (τ (τ (M.op (M.op (M.op X0 X1) X0) X0)))) X2) = (M.op (σ (τ (τ (M.op (M.op (M.op X0 X1) X0) X0)))) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq553 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq564 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op (M.op X0 X1) X0) X0)) X2) = (M.op (σ (M.op (M.op (M.op X0 X1) X0) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq545 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq569 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X0 X1) X0) X0)) X2) = (M.op (τ (M.op (M.op (M.op X0 X1) X0) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq558 X0 X1 X2
       have i₂ := eq11 (τ (M.op (M.op (M.op X0 X1) X0) X0))
       grind)
    | exact superpose eq11 eq558
    | exact resolve eq558 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq576 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op (M.op X0 X1) X0) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq564 X0 X1 X2
       have i₂ := eq72 X2 X0 X1
       grind)
    | exact superpose eq72 eq564
    | exact resolve eq564 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq564
  have eq580 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op (M.op X0 X1) X0) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq569 X0 X1 X2
       have i₂ := eq71 X2 X0 X1
       grind)
    | exact superpose eq71 eq569
    | exact resolve eq569 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq569
  have eq1536 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1)))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))))) X0
       have i₂ := eq222 (σ X0) X1 X2
       grind)
    | exact superpose eq222 eq24
    | exact resolve eq24 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq1548 : ∀ X0 X1 X2 : G, (k (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1)))))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1536 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1536
    | exact resolve eq1536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq2490 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1)))))) X0
       have i₂ := eq1548 (σ X0) X1 X2
       grind)
    | exact superpose eq1548 eq24
    | exact resolve eq24 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq2503 : ∀ X0 X1 X2 : G, (k (τ (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))))))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2490 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2490
    | exact resolve eq2490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2490
  have eq3505 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (τ (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1)))))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (τ (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))))))) X0
       have i₂ := eq2503 (σ X0) X1 X2
       grind)
    | exact superpose eq2503 eq24
    | exact resolve eq24 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq3518 : ∀ X0 X1 X2 : G, (k (τ (τ (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1)))))))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3505 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3505
    | exact resolve eq3505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505
  have eq4629 : ∀ X0 X1 X2 : G, (k (σ (k (τ X0) X1)) X2) = (M.op (k X0 (σ X1)) (σ (τ X2))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ (τ X2))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k (τ X0) X1)
       have i₂ := eq226 X0 X1 (τ X2)
       grind)
    | exact superpose eq226 eq18
    | (have j1 := eq226 X0 X1 (τ X2)
       grind)
    | exact resolve eq18 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq4667 : ∀ X0 X1 X2 : G, (k (σ (k (τ X0) X1)) X2) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ (τ X2))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4629 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq4629
    | (have j0 := eq4629 X0 X1 X2
       grind)
    | exact resolve eq4629 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4629
  have eq4682 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) X2) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ (τ X2))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4667 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq4667
    | (have j0 := eq4667 X0 X1 X2
       grind)
    | exact resolve eq4667 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4667
  have eq4697 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) X2) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4682 X0 X1 X2
       have j1 := eq12 (k X0 (σ X1)) X2
       grind)
    | (have r₁ := eq4682 X0 X1 X2
       have r₂ := eq12 (k X0 (σ X1)) X1
       grind)
    | exact resolve eq4682 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq4712 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) X2) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4697 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq4697
    | (have j0 := eq4697 X0 X1 X2
       grind)
    | exact resolve eq4697 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4697
  have eq4891 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (τ (τ (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))))))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (τ (τ (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1)))))))) X0
       have i₂ := eq3518 (σ X0) X1 X2
       grind)
    | exact superpose eq3518 eq24
    | exact resolve eq24 eq3518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3518
  have eq4904 : ∀ X0 X1 X2 : G, (k (τ (τ (τ (τ (τ (τ (τ (τ (M.op (M.op (M.op X1 X2) X1) X1))))))))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4891 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4891
    | exact resolve eq4891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4891
  have eq15785 : ∀ X0 X3 : G, (k (σ X0) X3) = (M.op (σ X0) X3) ∨ (σ X0) = (M.op (σ X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq4712 (τ (τ (τ (τ (τ (τ (τ (τ (M.op (M.op (M.op x x) x) x))))))))) x x
       have i₂ := eq4904 (σ x) x x
       grind)
    | exact superpose eq4904 eq4712
    | exact resolve eq4712 eq4904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4712 eq4904
  have eq15865 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15785 (τ X0) x
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15785
    | exact resolve eq15785 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15904 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq15785 X0 (σ X1)
       grind)
    | exact superpose eq15785 eq15
    | (have j1 := eq15785 X0 (σ X1)
       grind)
    | exact resolve eq15 eq15785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15785
  have eq16061 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq15865 X0 (τ X1)
       grind)
    | exact superpose eq15865 eq18
    | (have j1 := eq15865 X0 (τ X1)
       grind)
    | exact resolve eq18 eq15865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq15865
  have eq16907 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16061 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16061
    | exact resolve eq16061 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16061
  have eq17070 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16907 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq16907
    | (have j0 := eq16907 X0 X1
       grind)
    | exact resolve eq16907 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16907
  have eq17819 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15904 x y
       grind)
    | exact superpose eq15904 eq16
    | (have j1 := eq15904 x y
       grind)
    | exact resolve eq16 eq15904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15904
  have eq19279 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17819
       have i₂ := eq17070 y x
       grind)
    | exact superpose eq17070 eq17819
    | (have j1 := eq17070 (σ y) (σ x)
       grind)
    | (have r₁ := eq17819
       have r₂ := eq17070 y x
       grind)
    | exact resolve eq17819 eq17070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17070
  have eq19282 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19279
  have eq19285 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op (M.op x x) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq19282
       grind)
    | exact superpose eq19282 eq9
    | exact resolve eq9 eq19282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19282
  have eq19573 : ∀ X0 X1 : G, (M.op (M.op (M.op x x) x) X1) = X1 ∨ (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq19285 X1
       grind)
    | exact superpose eq19285 eq9
    | (have j1 := eq19285 X1
       grind)
    | exact resolve eq9 eq19285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19285
  have eq69652 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X2) = X2 ∨ (M.op (M.op (M.op X0 x) x) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 x x x
       have i₂ := eq19573 X0 x
       grind)
    | exact superpose eq19573 eq19
    | (have j1 := eq19573 X2 X1
       grind)
    | exact resolve eq19 eq19573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq19573
  have eq80764 : ∀ X0 X1 X2 : G, (M.op (τ (σ x)) X0) = X0 ∨ (M.op (M.op (M.op X1 x) x) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq580 (σ x) (σ x) X0
       have i₂ := eq69652 X1 X2 (σ x)
       grind)
    | exact superpose eq69652 eq580
    | (have j1 := eq69652 X1 X2 X2
       grind)
    | exact resolve eq580 eq69652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq69652
  have eq81143 : ∀ X0 X1 X2 : G, (M.op x X0) = X0 ∨ (M.op (M.op (M.op X1 x) x) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80764 X0 X1 X2
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq80764
    | (have j0 := eq80764 X0 X1 X2
       grind)
    | exact resolve eq80764 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80764
  have eq81191 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 x) x) X1) = X1 ∨ (M.op (M.op (M.op X2 x) x) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq81143 X0 X2 X3
       grind)
    | exact superpose eq81143 eq9
    | (have j1 := eq81143 X0 X0 X1
       grind)
    | exact resolve eq9 eq81143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81143
  have eq93959 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op (M.op (M.op X0 x) x) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq81191 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81191
  have eq93960 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) x) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq93959 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93959
  have eq94042 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq93960 x x
       grind)
    | exact superpose eq93960 eq9
    | exact resolve eq9 eq93960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94044 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 x x X0
       have i₂ := eq93960 x x
       grind)
    | exact superpose eq93960 eq35
    | exact resolve eq35 eq93960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq94070 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq576 x x X0
       have i₂ := eq93960 x x
       grind)
    | exact superpose eq93960 eq576
    | exact resolve eq576 eq93960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq93960
  have eq95095 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17819
       have i₂ := eq94044 y
       grind)
    | exact superpose eq94044 eq17819
    | exact resolve eq17819 eq94044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17819 eq94044
  have eq95330 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq95095
       have i₂ := eq94042 y
       grind)
    | exact superpose eq94042 eq95095
    | exact resolve eq95095 eq94042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95095
  have eq95331 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq95330
  have eq95365 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq95331
       have i₂ := eq94070 (σ y)
       grind)
    | exact superpose eq94070 eq95331
    | exact resolve eq95331 eq94070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95331
  have eq95522 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95365
       grind)
    | exact superpose eq95365 eq16
    | exact resolve eq16 eq95365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95736 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq95522
       have i₂ := eq94070 (σ x)
       grind)
    | exact superpose eq94070 eq95522
    | exact resolve eq95522 eq94070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94070 eq95522
  have eq95775 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq95736
       have i₂ := eq94042 y
       grind)
    | exact superpose eq94042 eq95736
    | exact resolve eq95736 eq94042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94042 eq95736
  have eq95803 : False := by grind
  exact eq95803

/-- `Equation3201`: `x = (((y ◇ z) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pxy_pxy_y_pxy_Equation3201 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3201 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3201.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq43
    | exact resolve eq43 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq49
    | exact resolve eq49 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq70
    | exact resolve eq70 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq69
    | exact resolve eq69 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq69
  have eq78 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ y = (k x y) := by
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
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq44
    | (have j1 := eq90 x y
       grind)
    | exact resolve eq44 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq128 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq126
    | exact resolve eq126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq129 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq128
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq128
    | exact resolve eq128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq129 eq90
    | (have j0 := eq90 (σ x) (σ y)
       grind)
    | exact resolve eq90 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq748
    | exact resolve eq748 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq752 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq749
       have r₂ := eq27
       grind)
    | exact resolve eq749 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq754 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq752
    | exact resolve eq752 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq756 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq754 eq79
    | (have r₁ := eq79
       have r₂ := eq754
       grind)
    | exact resolve eq79 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq762 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq754 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | exact resolve eq13 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq763 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq756
  have eq956 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq763 eq762
    | (have j0 := eq762 (σ y)
       grind)
    | (have r₁ := eq762 (σ y)
       have r₂ := eq763
       grind)
    | exact resolve eq762 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq763
  have eq957 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq956
  have eq958 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq957
  have eq964 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq958
    | exact resolve eq958 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq129 eq964
    | exact resolve eq964 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq964 eq129
    | exact resolve eq129 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq964
  have eq1007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq1003
  have eq1008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1001
  have eq1009 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1007
       have r₂ := eq27
       grind)
    | exact resolve eq1007 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1010 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1008
       have r₂ := eq27
       grind)
    | exact resolve eq1008 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1013 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq72
    | exact resolve eq72 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1019 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x y) ∨ (k x X0) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq13
    | (have j0 := eq13 x X0
       grind)
    | exact resolve eq13 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1022 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq1013
    | exact resolve eq1013 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1042 : (τ (σ y)) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1009 eq57
    | exact resolve eq57 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1009
  have eq1048 : (M.op x y) = (M.op x x) ∨ y = (k x y) := by
    first
    | exact superpose eq29 eq1042
    | exact resolve eq1042 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1053 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq1048
       grind)
    | exact superpose eq1048 eq78
    | (have r₁ := eq78
       have r₂ := eq1048
       grind)
    | exact resolve eq78 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1048
  have eq1062 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) := by grind
  clear eq1053
  have eq1063 : (M.op x y) = (M.op y y) ∨ y = (k x y) := by grind
  clear eq1062
  have eq1409 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1019 y
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq1019
    | (have j0 := eq1019 y
       grind)
    | (have r₁ := eq1019 y
       have r₂ := eq1063
       grind)
    | exact resolve eq1019 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq1063
  have eq1417 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by grind
  clear eq1409
  have eq1423 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1417
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1417
    | exact resolve eq1417 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1427 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1423
       grind)
    | exact superpose eq1423 eq44
    | exact resolve eq44 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq1430 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | exact superpose eq20 eq1427
    | exact resolve eq1427 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | exact superpose eq1430 eq90
    | (have j0 := eq90 (σ x) (σ y)
       grind)
    | exact resolve eq90 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq1437
    | exact resolve eq1437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1444 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq1441
       have r₂ := eq27
       grind)
    | exact resolve eq1441 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq1446 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq1444
    | exact resolve eq1444 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444
  have eq1451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | exact superpose eq1446 eq1022
    | exact resolve eq1022 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by grind
  clear eq1451
  have eq1473 : y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1469
       have r₂ := eq27
       grind)
    | exact resolve eq1469 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1479 : (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1473
       grind)
    | exact superpose eq1473 eq44
    | exact resolve eq44 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1473
  have eq1483 : (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1479
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1479
    | exact resolve eq1479 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1494 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1483 eq90
    | (have j0 := eq90 (σ x) (σ y)
       grind)
    | exact resolve eq90 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1483
  have eq1499 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq1494
    | exact resolve eq1494 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq1502 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq1499
    | exact resolve eq1499 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1502 eq1022
    | exact resolve eq1022 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq1502
  have eq1524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1508
  have eq1527 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1524
       have r₂ := eq27
       grind)
    | exact resolve eq1524 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq1530 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1527 eq51
    | exact resolve eq51 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1527
  have eq1592 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f1592_13 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ (σ y) = (σ (M.op x y)) := by
      intro X0
      grind
    have f1592_19 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f1592_21 : X0 ≠ (M.op (σ x) X0) := by grind
    have f1592_22 : (σ y) ≠ (σ (M.op x y)) := by grind
    have f1592_24 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 := by
      intro X0
      first
      | (have j0 := f1592_13 X0
         grind)
      | (have r₁ := f1592_13 X0
         have r₂ := f1592_22
         grind)
      | exact resolve f1592_13 f1592_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1592_28 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f1592_19 X0 (σ y) (σ x)
         have i₂ := f1592_24 (σ x)
         grind)
      | exact superpose f1592_24 f1592_19
      | exact resolve f1592_19 f1592_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1592_37 : X0 ≠ X0 := by
      first
      | (have i₁ := f1592_21
         have i₂ := f1592_28 X0
         grind)
      | exact superpose f1592_28 f1592_21
      | (have r₁ := f1592_21
         have r₂ := f1592_28 X0
         grind)
      | exact resolve f1592_21 f1592_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1592_42 : False := by grind
    exact f1592_42
  clear eq1530
  have eq1668 : (τ (σ x)) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1592 eq71
    | exact resolve eq71 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1592
  have eq1700 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28 eq1668
    | exact resolve eq1668 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1668
  have eq1934 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq1700
       grind)
    | exact superpose eq1700 eq14
    | exact resolve eq14 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq7813 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq1934 x
       grind)
    | exact superpose eq1934 eq14
    | exact resolve eq14 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934
  have eq7872 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7813 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7813
    | (have j0 := eq7813 y
       grind)
    | exact resolve eq7813 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7813
  have eq7937 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7872 eq29
    | exact resolve eq29 eq7872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7872
  have eq7985 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq7937
    | exact resolve eq7937 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7937
  have eq7986 : y = (M.op x y) := by grind
  clear eq7985
  have eq7989 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq7986 eq20
    | exact resolve eq20 eq7986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq7991 : ∀ X0 : G, (M.op (M.op (M.op y x) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq7986 eq50
    | exact resolve eq50 eq7986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq7986
  have eq8043 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq7989
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7989
    | exact resolve eq7989 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7989
  have eq8048 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq8043 eq26
    | exact resolve eq26 eq8043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8043
  have eq8274 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq7991 x
       grind)
    | exact superpose eq7991 eq14
    | exact resolve eq14 eq7991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7991
  have eq8352 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq8274 x
       grind)
    | exact superpose eq8274 eq72
    | exact resolve eq72 eq8274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq8274
  have eq8411 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8352
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8352
    | exact resolve eq8352 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8352
  have eq8444 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq8411 eq14
    | exact resolve eq14 eq8411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8457 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq8411 eq8444
    | exact resolve eq8444 eq8411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8444
  have eq8470 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq8411 eq8457
    | exact resolve eq8457 eq8411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8411 eq8457
  have eq8502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8470 eq8048
    | exact resolve eq8048 eq8470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8048 eq8470
  have eq8567 : False := by grind
  exact eq8567

/-- `Equation3201`: `x = (((y ◇ z) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pxy_Equation3201 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3201 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3201.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
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
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq97 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq100 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq100
  have eq108 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq97
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq5537 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq92 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq92
    | (have j0 := eq92 x
       grind)
    | exact resolve eq92 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq5547 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5537
  have eq5550 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5547
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq5547
    | exact resolve eq5547 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5547
  have eq5566 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5550
       have r₂ := eq13 (σ x) x
       grind)
    | exact resolve eq5550 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5550
  have eq5570 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5566 eq49
    | exact resolve eq49 eq5566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq5696 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq93 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq93
    | (have j0 := eq93 y
       grind)
    | exact resolve eq93 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq5705 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5696
  have eq5707 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5705
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq5705
    | exact resolve eq5705 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5705
  have eq5730 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5707
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq5707 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5707
  have eq5743 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5730 eq85
    | exact resolve eq85 eq5730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq12889 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5730 eq107
    | exact resolve eq107 eq5730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq12890 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5566 eq108
    | exact resolve eq108 eq5566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq17056 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq12889
       grind)
    | exact superpose eq12889 eq16
    | exact resolve eq16 eq12889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12889
  have eq17113 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5743 eq17056
    | exact resolve eq17056 eq5743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17056
  have eq17116 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq17113
       have r₂ := eq13 y x
       grind)
    | exact resolve eq17113 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17113
  have eq17117 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq17116
       grind)
    | exact superpose eq17116 eq72
    | exact resolve eq72 eq17116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq17150 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq5730 eq17117
    | exact resolve eq17117 eq5730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5730 eq17117
  have eq17224 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq12890
       grind)
    | exact superpose eq12890 eq16
    | exact resolve eq16 eq12890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12890
  have eq17283 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5570 eq17224
    | exact resolve eq17224 eq5570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17224
  have eq17286 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq17283
       have r₂ := eq13 x x
       grind)
    | exact resolve eq17283 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17283
  have eq17287 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq17286
       grind)
    | exact superpose eq17286 eq43
    | exact resolve eq43 eq17286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq17320 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq5566 eq17287
    | exact resolve eq17287 eq5566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5566 eq17287
  have eq24284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq24285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq24284
    | exact resolve eq24284 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24284
  have eq24296 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24285
       have r₂ := eq27
       grind)
    | exact resolve eq24285 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24285
  have eq24300 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24296 eq5743
    | exact resolve eq5743 eq24296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5743 eq24296
  have eq24333 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24300
       have i₂ := eq17116
       grind)
    | exact superpose eq17116 eq24300
    | exact resolve eq24300 eq17116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17116 eq24300
  have eq24342 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq24333
    | exact resolve eq24333 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq24333
  have eq24343 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq24342
  have eq24345 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24343 eq5570
    | exact resolve eq5570 eq24343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5570 eq24343
  have eq24378 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24345
       have i₂ := eq17286
       grind)
    | exact superpose eq17286 eq24345
    | exact resolve eq24345 eq17286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17286 eq24345
  have eq24387 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq24378
    | exact resolve eq24378 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24378
  have eq24388 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq24387
  have eq24396 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17150
       have i₂ := eq24388
       grind)
    | exact superpose eq24388 eq17150
    | exact resolve eq17150 eq24388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17150
  have eq24400 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq24388
       grind)
    | exact superpose eq24388 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq24388
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq24388
       grind)
    | exact resolve eq13 eq24388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24388
  have eq24413 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq24400 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24400
  have eq24417 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24396
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24396
    | exact resolve eq24396 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24396
  have eq24869 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq24417 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq24417
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq24417
       grind)
    | exact resolve eq13 eq24417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24417
  have eq24882 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq24869 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24869
  have eq24968 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq24413 x
       grind)
    | exact superpose eq24413 eq71
    | exact resolve eq71 eq24413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq24413
  have eq25008 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24968
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24968
    | exact resolve eq24968 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24968
  have eq25035 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq25008
    | exact resolve eq25008 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25008
  have eq25666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24882 eq25035
    | exact resolve eq25035 eq24882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24882 eq25035
  have eq25676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq25666
  have eq25678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq25676
    | exact resolve eq25676 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25676
  have eq25708 : x = (M.op x x) := by
    first
    | (have r₁ := eq25678
       have r₂ := eq27
       grind)
    | exact resolve eq25678 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25678
  have eq25719 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17320
       have i₂ := eq25708
       grind)
    | exact superpose eq25708 eq17320
    | exact resolve eq17320 eq25708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17320
  have eq25724 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq25708
       grind)
    | exact superpose eq25708 eq14
    | exact resolve eq14 eq25708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25749 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25724 X0
       have i₂ := eq25708
       grind)
    | exact superpose eq25708 eq25724
    | exact resolve eq25724 eq25708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25724
  have eq25752 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25719
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25719
    | exact resolve eq25719 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25719
  have eq25770 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25749 X0
       have i₂ := eq25708
       grind)
    | exact superpose eq25708 eq25749
    | exact resolve eq25749 eq25708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25708 eq25749
  have eq25785 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq25752 eq14
    | exact resolve eq14 eq25752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25810 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq25752 eq25785
    | exact resolve eq25785 eq25752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25785
  have eq25831 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq25752 eq25810
    | exact resolve eq25810 eq25752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25752 eq25810
  have eq25843 : y = (M.op x y) := by
    first
    | (have i₁ := eq25770 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25770
    | (have j0 := eq25770 y
       grind)
    | exact resolve eq25770 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25770
  have eq25925 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq25843 eq20
    | exact resolve eq20 eq25843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq25843
  have eq26078 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25925
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25925
    | exact resolve eq25925 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25925
  have eq27215 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25831 eq26
    | (have j1 := eq25831 (σ y)
       grind)
    | exact resolve eq26 eq25831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq25831
  have eq27278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26078 eq27215
    | exact resolve eq27215 eq26078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26078 eq27215
  have eq27289 : False := by grind
  exact eq27289

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_x_pxy_y_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
  clear eq24 eq35
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq43
    | exact resolve eq43 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq75 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq72
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq72
  have eq88 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq44
    | (have j1 := eq88 x y
       grind)
    | exact resolve eq44 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
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
  have eq130 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq127
    | exact resolve eq127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq1089 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq130 eq88
    | (have j0 := eq88 (σ x) (σ y)
       grind)
    | exact resolve eq88 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1089
    | exact resolve eq1089 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1093 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1090
       have r₂ := eq27
       grind)
    | exact resolve eq1090 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1097 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1093 eq14
    | exact resolve eq14 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1093 eq1097
    | exact resolve eq1097 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093 eq1097
  have eq1209 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1196
  have eq1216 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1209 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1209
       grind)
    | exact resolve eq13 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1223 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1216
  have eq1230 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1223
    | exact resolve eq1223 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1230 eq130
    | exact resolve eq130 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq1230
  have eq1358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1355
  have eq1360 : x = (M.op y x) := by
    first
    | (have r₁ := eq1358
       have r₂ := eq27
       grind)
    | exact resolve eq1358 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1364 : ∀ X0 : G, (M.op x x) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq1360
       grind)
    | exact superpose eq1360 eq14
    | exact resolve eq14 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1375 : (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq1364 y
       have i₂ := eq1360
       grind)
    | exact superpose eq1360 eq1364
    | exact resolve eq1364 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq1391 : x = (M.op x x) := by
    first
    | (have i₁ := eq1375
       have i₂ := eq1360
       grind)
    | exact superpose eq1360 eq1375
    | exact resolve eq1375 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360 eq1375
  have eq1525 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1391
       grind)
    | exact superpose eq1391 eq75
    | exact resolve eq75 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1528 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1391
       grind)
    | exact superpose eq1391 eq13
    | (have j0 := eq13 x X0
       grind)
    | exact resolve eq13 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391
  have eq1543 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1528 X0
       have j1 := eq88 x X0
       grind)
    | (have r₁ := eq1528 x
       have r₂ := eq88 x x
       grind)
    | exact resolve eq1528 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq1544 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1525
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1525
    | exact resolve eq1525 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1525
  have eq1591 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq1544 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | exact resolve eq13 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1606 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq1591 X0
       have j1 := eq88 (σ x) X0
       grind)
    | (have r₁ := eq1591 x
       have r₂ := eq88 (σ x) x
       grind)
    | exact resolve eq1591 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq1591
  have eq1994 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1543 y
       grind)
    | exact superpose eq1543 eq44
    | exact resolve eq44 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1543
  have eq1996 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1994
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1994
    | exact resolve eq1994 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1994
  have eq1999 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1996
    | exact resolve eq1996 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1996
  have eq2370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1606 eq1999
    | exact resolve eq1999 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606 eq1999
  have eq2375 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2370
    | exact resolve eq2370 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2370
  have eq2383 : False := by grind
  exact eq2383

/-- `Equation3929`: `x ◇ y = (x ◇ (y ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pxx_x_Equation3929 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law3929 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3929.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
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
  clear eq18
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X1)) X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq63 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq63 X0 X1 X2
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 x (M.op X0 X1)
       have r₂ := eq63 X0 X1 x
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq84 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq82 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq865 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq865 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq865 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq865 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq909 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 (σ X0) X1
       have i₂ := eq866 (σ X0)
       grind)
    | exact superpose eq866 eq26
    | exact resolve eq26 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq922 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq909 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq909
    | exact resolve eq909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq949 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq922 X0 X1
       have i₂ := eq866 X0
       grind)
    | exact superpose eq866 eq922
    | exact resolve eq922 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq922
  have eq971 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq949 X0 X1
       have i₂ := eq84 X0 X0 X1
       grind)
    | exact superpose eq84 eq949
    | exact resolve eq949 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq989 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq971 X0 X1
       have i₂ := eq67 X1 X0
       grind)
    | exact superpose eq67 eq971
    | exact resolve eq971 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq1001 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1
       have i₂ := eq84 (σ X0) (σ X0) (σ X1)
       grind)
    | exact superpose eq84 eq989
    | exact resolve eq989 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq989
  have eq1011 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1001 X0 X1
       have i₂ := eq67 (σ X1) (σ X0)
       grind)
    | exact superpose eq67 eq1001
    | exact resolve eq1001 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1001
  have eq1114 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1011 y x
       grind)
    | exact superpose eq1011 eq16
    | (have r₁ := eq16
       have r₂ := eq1011 y x
       grind)
    | exact resolve eq16 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1136 : False := by grind
  exact eq1136
