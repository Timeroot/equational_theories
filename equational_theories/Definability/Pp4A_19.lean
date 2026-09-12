import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_y_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
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
  have eq176 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq16 X0 x x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 X1 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq176 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x y X0
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x) (σ y) X0
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq176 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 X0 x y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 X0 (σ x) (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq176 X2 X0 x
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq183 eq176
    | exact resolve eq176 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq182 (M.op x x)
       have i₂ := eq176 x x x
       grind)
    | exact superpose eq176 eq182
    | exact resolve eq182 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op X0 X0) X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq176
    | exact resolve eq176 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : x = (M.op (k (M.op x x) x) (M.op x y)) := by
    first
    | (have i₁ := eq187 (M.op x x)
       have i₂ := eq182 x
       grind)
    | exact superpose eq182 eq187
    | exact resolve eq187 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
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
  have eq765 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq785 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq182 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq182
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 (M.op (k X0 X1) X2)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 X0 x
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq177
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 X1 : G, x = (M.op (k x (M.op X0 X1)) (M.op x y)) ∨ x = (M.op (M.op X0 X1) x) ∨ x = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq11 x (M.op X0 X1)
       grind)
    | exact superpose eq11 eq178
    | (have j1 := eq11 x (M.op X0 X1)
       grind)
    | exact resolve eq178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq836 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq837 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq837 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq843 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq788 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq948 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq190 X0 X0 X0
       have i₂ := eq708 X0
       grind)
    | exact superpose eq708 eq190
    | exact resolve eq190 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq782
       grind)
    | exact superpose eq782 eq39
    | exact resolve eq39 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1187
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1187
    | exact resolve eq1187 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1190 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1188
    | exact resolve eq1188 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1190 eq785
    | exact resolve eq785 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1304 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1297
       have r₂ := eq27
       grind)
    | exact resolve eq1297 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1308 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1304
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq1304
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq1304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1312 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1304 eq182
    | exact resolve eq182 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1313 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1304 eq708
    | exact resolve eq708 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1318 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1304 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1304 eq176
    | exact resolve eq176 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1334 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1318
  have eq1335 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1308
  have eq1339 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq1313
    | exact resolve eq1313 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1340 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1190 eq1312
    | exact resolve eq1312 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1412 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1340 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1413 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1340 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1340
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1340
       grind)
    | exact resolve eq12 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1429 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1339 eq1413
    | exact resolve eq1413 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1430 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1429
  have eq1431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1339 eq1412
    | exact resolve eq1412 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1431
       have r₂ := eq1430
       grind)
    | exact resolve eq1431 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430 eq1431
  have eq1436 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1434
       have r₂ := eq27
       grind)
    | exact resolve eq1434 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq1497 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1436
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq1436
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq1436 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1507 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1436 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436
  have eq1523 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1507
  have eq1524 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1497
  have eq1532 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1523 eq1524
    | exact resolve eq1524 eq1523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq1533 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq836 (σ X1) (σ X0)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq836
    | (have j0 := eq836 (σ X1) (σ X0)
       grind)
    | exact resolve eq836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1909 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1334 eq97
    | exact resolve eq97 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1919 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq1909
    | exact resolve eq1909 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909
  have eq1942 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1523 eq115
    | exact resolve eq115 eq1523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1952 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq1942
    | exact resolve eq1942 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942
  have eq1968 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq708 x
       have i₂ := eq1952
       grind)
    | exact superpose eq1952 eq708
    | exact resolve eq708 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1971 : y = (M.op (k x y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq948 x
       have i₂ := eq1952
       grind)
    | exact superpose eq1952 eq948
    | exact resolve eq948 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1977 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq176 X0 x x
       have i₂ := eq1952
       grind)
    | exact superpose eq1952 eq176
    | exact resolve eq176 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1991 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1968
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1968
    | exact resolve eq1968 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968
  have eq2735 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1335 eq97
    | exact resolve eq97 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq2748 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq31 eq2735
    | exact resolve eq2735 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq2826 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq2748 eq708
    | exact resolve eq708 eq2748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq2859 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq1304 eq2826
    | exact resolve eq2826 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq2864 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq1919 eq2859
    | exact resolve eq2859 eq1919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919 eq2859
  have eq2892 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1532 eq115
    | exact resolve eq115 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1532
  have eq2902 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq2892
    | exact resolve eq2892 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892
  have eq2988 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq2864 eq141
    | exact resolve eq141 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3001 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq2988
    | exact resolve eq2988 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988
  have eq3011 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k y y) := by
    first
    | exact superpose eq2902 eq1322
    | exact resolve eq1322 eq2902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq3015 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k y y) := by
    first
    | exact superpose eq2902 eq708
    | exact resolve eq708 eq2902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902
  have eq3041 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k y y) := by grind
  clear eq3011
  have eq3048 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k y y) := by
    first
    | exact superpose eq1304 eq3015
    | exact resolve eq3015 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015
  have eq3050 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq26 eq3041
    | exact resolve eq3041 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041
  have eq3053 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k y y) := by
    first
    | exact superpose eq1952 eq3048
    | exact resolve eq3048 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048
  have eq3060 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq708 x
       have i₂ := eq3050
       grind)
    | exact superpose eq3050 eq708
    | exact resolve eq708 eq3050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3063 : y = (M.op (k x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq948 x
       have i₂ := eq3050
       grind)
    | exact superpose eq3050 eq948
    | exact resolve eq948 eq3050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3069 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq176 X0 x x
       have i₂ := eq3050
       grind)
    | exact superpose eq3050 eq176
    | exact resolve eq176 eq3050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3086 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq3060
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3060
    | exact resolve eq3060 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3060
  have eq3146 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3001
       grind)
    | exact superpose eq3001 eq39
    | exact resolve eq39 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3156 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq3146
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3146
    | exact resolve eq3146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3146
  have eq3158 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq3156
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3156
    | exact resolve eq3156 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3255 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1971
       have i₂ := eq1991
       grind)
    | exact superpose eq1991 eq1971
    | exact resolve eq1971 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971 eq1991
  have eq3283 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq3255
  have eq3334 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq3283 eq1977
    | exact resolve eq1977 eq3283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977 eq3283
  have eq3361 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq3334
  have eq3921 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k y y) := by
    first
    | exact superpose eq3053 eq141
    | exact resolve eq141 eq3053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3053
  have eq3934 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq3921
    | exact resolve eq3921 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq4064 : y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq3063
       have i₂ := eq3086
       grind)
    | exact superpose eq3086 eq3063
    | exact resolve eq3063 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063 eq3086
  have eq4098 : y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by grind
  clear eq4064
  have eq4158 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq4098 eq3069
    | exact resolve eq3069 eq4098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3069 eq4098
  have eq4191 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq4158
  have eq4503 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq708 x
       have i₂ := eq3934
       grind)
    | exact superpose eq3934 eq708
    | exact resolve eq708 eq3934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4506 : y = (M.op (k x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq948 x
       have i₂ := eq3934
       grind)
    | exact superpose eq3934 eq948
    | exact resolve eq948 eq3934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq4512 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq176 X0 x x
       have i₂ := eq3934
       grind)
    | exact superpose eq3934 eq176
    | exact resolve eq176 eq3934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3934
  have eq4536 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq4503
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4503
    | exact resolve eq4503 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4503
  have eq7806 : y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq4506
       have i₂ := eq4536
       grind)
    | exact superpose eq4536 eq4506
    | exact resolve eq4506 eq4536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4506 eq4536
  have eq7854 : y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (k y y) := by grind
  clear eq7806
  have eq7937 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq7854 eq4512
    | exact resolve eq4512 eq7854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4512 eq7854
  have eq7990 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (M.op y y) := by grind
  clear eq7937
  have eq8015 : x ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq836 y y
       have i₂ := eq7990
       grind)
    | exact superpose eq7990 eq836
    | (have j0 := eq836 y y
       grind)
    | (have r₁ := eq836 x x
       have r₂ := eq7990
       grind)
    | exact resolve eq836 eq7990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7990
  have eq8016 : x ≠ y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) ∨ x = (M.op y y) := by grind
  clear eq8015
  have eq16278 : (k y x) = (M.op y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq843 x
       have i₂ := eq3001
       grind)
    | exact superpose eq3001 eq843
    | (have j0 := eq843 x
       grind)
    | exact resolve eq843 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001
  have eq16289 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq843 y
       have i₂ := eq3361
       grind)
    | exact superpose eq3361 eq843
    | (have j0 := eq843 y
       grind)
    | exact resolve eq843 eq3361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3361
  have eq16290 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq843 y
       have i₂ := eq4191
       grind)
    | exact superpose eq4191 eq843
    | (have j0 := eq843 y
       grind)
    | exact resolve eq843 eq4191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4191
  have eq16299 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq2864 eq843
    | (have j0 := eq843 (σ x)
       grind)
    | exact resolve eq843 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864
  have eq16437 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq16299
       have r₂ := eq13 (k (σ x) (σ x)) (σ x)
       grind)
    | (have r₁ := eq16299
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq16299
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16299 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16299
  have eq16446 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq16290
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq16290
       have r₂ := eq13 x y
       grind)
    | exact resolve eq16290 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16290
  have eq16447 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq16289
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq16289
       have r₂ := eq13 x y
       grind)
    | exact resolve eq16289 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16289
  have eq16451 : (k y x) = (M.op y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16278
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq16278
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16278 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16278
  have eq16474 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq1304 eq16437
    | exact resolve eq16437 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq16437
  have eq16479 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16446
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16446
    | exact resolve eq16446 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16446
  have eq16480 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16447
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16447
    | exact resolve eq16447 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16447
  have eq16481 : (k y x) = (M.op y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq838 x
       grind)
    | (have r₁ := eq16451
       have r₂ := eq838 x
       grind)
    | exact resolve eq16451 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16451
  have eq16489 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq3158 eq16474
    | exact resolve eq16474 eq3158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3158 eq16474
  have eq16500 : x = (M.op (k y x) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq187 y
       have i₂ := eq16481
       grind)
    | exact superpose eq16481 eq187
    | exact resolve eq187 eq16481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16481
  have eq16675 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16489 eq97
    | exact resolve eq97 eq16489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq16489
  have eq16718 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq31 eq16675
    | exact resolve eq16675 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16675
  have eq16822 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq16480
       grind)
    | exact superpose eq16480 eq40
    | exact resolve eq40 eq16480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16480
  have eq16844 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16822
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16822
    | exact resolve eq16822 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16822
  have eq16846 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq16844
    | exact resolve eq16844 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16844
  have eq16867 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq16479
       grind)
    | exact superpose eq16479 eq40
    | exact resolve eq40 eq16479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16479
  have eq16889 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16867
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16867
    | exact resolve eq16867 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16867
  have eq16891 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16889
    | exact resolve eq16889 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16889
  have eq16898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16846 eq1339
    | exact resolve eq1339 eq16846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16846
  have eq16903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq16898
  have eq16910 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16903
       have r₂ := eq27
       grind)
    | exact resolve eq16903 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16903
  have eq16965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16891 eq1339
    | exact resolve eq1339 eq16891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq16891
  have eq16970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16965
  have eq16977 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16970
       have r₂ := eq27
       grind)
    | exact resolve eq16970 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16970
  have eq17033 : y = (M.op (k y y) y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq718 y y
       have i₂ := eq16910
       grind)
    | exact superpose eq16910 eq718
    | exact resolve eq718 eq16910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16910
  have eq17078 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1952 eq17033
    | exact resolve eq17033 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952 eq17033
  have eq17087 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17078
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17078
    | exact resolve eq17078 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17078
  have eq17088 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17087
  have eq17103 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq17088
       grind)
    | exact superpose eq17088 eq187
    | exact resolve eq187 eq17088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17116 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq708 x
       have i₂ := eq17088
       grind)
    | exact superpose eq17088 eq708
    | exact resolve eq708 eq17088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17126 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq176 X0 x x
       have i₂ := eq17088
       grind)
    | exact superpose eq17088 eq176
    | exact resolve eq176 eq17088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17088
  have eq17173 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17116
    | exact resolve eq17116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17116
  have eq17175 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17103 eq183
    | exact resolve eq183 eq17103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17103
  have eq17246 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq17173
       grind)
    | exact superpose eq17173 eq40
    | exact resolve eq40 eq17173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17173
  have eq17269 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17246
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17246
    | exact resolve eq17246 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17246
  have eq17271 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq17269
    | exact resolve eq17269 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17269
  have eq17716 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17175 eq17126
    | exact resolve eq17126 eq17175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17126 eq17175
  have eq17785 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17716
  have eq17869 : x = (k y y) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq17785
       grind)
    | exact superpose eq17785 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq17785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17785
  have eq17906 : x = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17869
  have eq19348 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq17906
       grind)
    | exact superpose eq17906 eq40
    | exact resolve eq40 eq17906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq17906
  have eq19361 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19348
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19348
    | exact resolve eq19348 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19348
  have eq19364 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19361
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19361
    | exact resolve eq19361 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19361
  have eq19369 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19364 eq843
    | (have j0 := eq843 (σ y)
       grind)
    | exact resolve eq843 eq19364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19379 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq19369
    | exact resolve eq19369 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19369
  have eq19383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17271 eq19379
    | exact resolve eq19379 eq17271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17271 eq19379
  have eq19386 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19383
       have r₂ := eq27
       grind)
    | exact resolve eq19383 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19383
  have eq19426 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19386 eq718
    | exact resolve eq718 eq19386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19386
  have eq19461 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19364 eq19426
    | exact resolve eq19426 eq19364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19364 eq19426
  have eq19471 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq19461
    | exact resolve eq19461 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19461
  have eq19472 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq19471
  have eq24966 : y = (M.op (k y y) y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq718 y y
       have i₂ := eq16977
       grind)
    | exact superpose eq16977 eq718
    | exact resolve eq718 eq16977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16977
  have eq25028 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3050 eq24966
    | exact resolve eq24966 eq3050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3050 eq24966
  have eq25038 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25028
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25028
    | exact resolve eq25028 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25028
  have eq25039 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25038
  have eq25069 : ∀ X0 : G, y ≠ X0 ∨ (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq25039
       grind)
    | exact superpose eq25039 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25039
       grind)
    | exact resolve eq13 eq25039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25078 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq25039
       grind)
    | exact superpose eq25039 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq25039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25082 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq176 X0 x x
       have i₂ := eq25039
       grind)
    | exact superpose eq25039 eq176
    | exact resolve eq176 eq25039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq25115 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25078
  have eq27551 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq25115
       grind)
    | exact superpose eq25115 eq39
    | exact resolve eq39 eq25115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27571 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27551
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27551
    | exact resolve eq27551 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27551
  have eq27575 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27571
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27571
    | exact resolve eq27571 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27571
  have eq27579 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19472 eq27575
    | exact resolve eq27575 eq19472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27575
  have eq27625 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27579 eq141
    | exact resolve eq141 eq27579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27579
  have eq27685 : x = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq27625
    | exact resolve eq27625 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27625
  have eq27819 : x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25115
       have i₂ := eq27685
       grind)
    | exact superpose eq27685 eq25115
    | exact resolve eq25115 eq27685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25115
  have eq27822 : (k x x) = (M.op x x) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq843 x
       have i₂ := eq27685
       grind)
    | exact superpose eq27685 eq843
    | (have j0 := eq843 x
       grind)
    | exact resolve eq843 eq27685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq27685
  have eq27840 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27819
  have eq27874 : (k x x) = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq27822
       have r₂ := eq13 (k x x) x
       grind)
    | (have r₁ := eq27822
       have r₂ := eq13 x x
       grind)
    | exact resolve eq27822 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27822
  have eq27877 : (k x x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq25069 x
       grind)
    | (have r₁ := eq27874
       have r₂ := eq25069 x
       grind)
    | (have r₁ := eq27874
       have r₂ := eq25069 (M.op x y)
       grind)
    | exact resolve eq27874 eq25069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25069 eq27874
  have eq27878 : y = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25039 eq27877
    | exact resolve eq27877 eq25039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25039 eq27877
  have eq27879 : x = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27840 eq27878
    | exact resolve eq27878 eq27840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27840 eq27878
  have eq27935 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq836 x x
       have i₂ := eq27879
       grind)
    | exact superpose eq27879 eq836
    | (have j0 := eq836 x x
       grind)
    | (have r₁ := eq836 x x
       have r₂ := eq27879
       grind)
    | exact resolve eq836 eq27879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27879
  have eq27939 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27935
  have eq27940 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27939
  have eq28036 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25082 x
       have i₂ := eq27940
       grind)
    | exact superpose eq27940 eq25082
    | exact resolve eq25082 eq27940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25082 eq27940
  have eq28089 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28036
  have eq28142 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28089
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28089
    | exact resolve eq28089 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28089
  have eq38743 : x = (M.op (k x x) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16500 eq810
    | exact resolve eq810 eq16500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq39023 : x = (M.op (k x x) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq38743
  have eq39529 : (k x x) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39023 eq795
    | (have j0 := eq795 x x x
       grind)
    | exact resolve eq795 eq39023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq39023
  have eq39588 : (k x x) = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq39529
  have eq39608 : (k x x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq39588
       have r₂ := eq13 (k x x) x
       grind)
    | (have r₁ := eq39588
       have r₂ := eq13 x x
       grind)
    | exact resolve eq39588 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39588
  have eq39629 : x = (M.op (k (k x x) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq724
       have i₂ := eq39608
       grind)
    | exact superpose eq39608 eq724
    | exact resolve eq724 eq39608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq39672 : (k (k x x) x) = (M.op (k x x) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq39608
       grind)
    | exact superpose eq39608 eq182
    | exact resolve eq182 eq39608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39608
  have eq40934 : x = (M.op (k y x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq39629
       have i₂ := eq16718
       grind)
    | exact superpose eq16718 eq39629
    | exact resolve eq39629 eq16718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39629
  have eq41007 : x = (M.op (k y x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq40934
  have eq41023 : x = (M.op (k y x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq16500 eq41007
    | exact resolve eq41007 eq16500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16500 eq41007
  have eq41024 : x = (M.op (k y x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq41023
  have eq41659 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41024
       have i₂ := eq782
       grind)
    | exact superpose eq782 eq41024
    | exact resolve eq41024 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41024
  have eq41726 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq41659
  have eq45304 : (k y x) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq39672
       have i₂ := eq16718
       grind)
    | exact superpose eq16718 eq39672
    | exact resolve eq39672 eq16718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16718 eq39672
  have eq45415 : (k y x) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq45304
  have eq45454 : (k y x) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq45415
       have r₂ := eq13 y x
       grind)
    | exact resolve eq45415 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45415
  have eq45475 : y = (M.op (M.op x y) (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq183 x
       have i₂ := eq45454
       grind)
    | exact superpose eq45454 eq183
    | exact resolve eq183 eq45454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45454
  have eq45724 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45475
       have i₂ := eq782
       grind)
    | exact superpose eq782 eq45475
    | exact resolve eq45475 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq45475
  have eq45791 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq45724
  have eq45798 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq41726 eq45791
    | exact resolve eq45791 eq41726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41726 eq45791
  have eq45799 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq45798
  have eq45855 : y = (k x x) ∨ x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq45799
       grind)
    | exact superpose eq45799 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq45799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45799
  have eq45904 : y = (k x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq45855
  have eq46054 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq45904
       grind)
    | exact superpose eq45904 eq39
    | exact resolve eq39 eq45904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46091 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq46054
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46054
    | exact resolve eq46054 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46054
  have eq46096 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq46091
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46091
    | exact resolve eq46091 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46091
  have eq46101 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19472 eq46096
    | exact resolve eq46096 eq19472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19472 eq46096
  have eq46525 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq46101 eq141
    | exact resolve eq141 eq46101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq46101
  have eq46586 : x = (k x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq46525
    | exact resolve eq46525 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46525
  have eq46821 : x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45904
       have i₂ := eq46586
       grind)
    | exact superpose eq46586 eq45904
    | exact resolve eq45904 eq46586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45904 eq46586
  have eq46843 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq46821
  have eq46894 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq46843 eq184
    | exact resolve eq184 eq46843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46895 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq46843 eq188
    | exact resolve eq188 eq46843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46901 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq46843 eq765
    | (have r₁ := eq765
       have r₂ := eq46843
       grind)
    | exact resolve eq765 eq46843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq46843
  have eq46905 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq46901
  have eq46908 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq46894 eq46894
    | exact resolve eq46894 eq46894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46894
  have eq47042 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq46908
  have eq47093 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq47042 eq708
    | exact resolve eq708 eq47042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47192 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq47042 eq47093
    | exact resolve eq47093 eq47042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47093
  have eq47234 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq47192 eq152
    | exact resolve eq152 eq47192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq47192
  have eq47285 : y = (k y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq47234
    | exact resolve eq47234 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47234
  have eq47323 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq836 y y
       have i₂ := eq47285
       grind)
    | exact superpose eq47285 eq836
    | (have j0 := eq836 y y
       grind)
    | (have r₁ := eq836 y y
       have r₂ := eq47285
       grind)
    | exact resolve eq836 eq47285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq47285
  have eq47327 : y ≠ y ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq47323
  have eq47328 : y = (M.op y y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq47327
  have eq47383 : y = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq47328
       grind)
    | exact superpose eq47328 eq183
    | exact resolve eq183 eq47328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq47328
  have eq57241 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq46905 eq46895
    | exact resolve eq46895 eq46905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46895 eq46905
  have eq57315 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq57241
  have eq57371 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq57315 eq1190
    | exact resolve eq1190 eq57315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57374 : (τ (σ x)) = (k y (τ (σ x))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq57315 eq107
    | exact resolve eq107 eq57315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq57315
  have eq57381 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq57371
  have eq57390 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq57374
    | exact resolve eq57374 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57374
  have eq57392 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq47042 eq57381
    | exact resolve eq57381 eq47042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57381
  have eq57507 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq57390 eq47042
    | exact resolve eq47042 eq57390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47042 eq57390
  have eq57637 : x = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq57507
  have eq74439 : x = (M.op (k y x) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq718 x x
       have i₂ := eq57392
       grind)
    | exact superpose eq57392 eq718
    | exact resolve eq718 eq57392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq57392
  have eq74549 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq57637 eq74439
    | exact resolve eq74439 eq57637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57637 eq74439
  have eq74564 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74549
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74549
    | exact resolve eq74549 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74549
  have eq74566 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq74564 eq31
    | exact resolve eq31 eq74564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq74564
  have eq74873 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq74566
    | exact resolve eq74566 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74566
  have eq74874 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq74873
  have eq74886 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq74874 eq28
    | exact resolve eq28 eq74874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq74874
  have eq75032 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq74886
    | exact resolve eq74886 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq74886
  have eq75033 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq75032
  have eq75036 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq75033
       grind)
    | exact superpose eq75033 eq18
    | exact resolve eq18 eq75033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75037 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq75033
       grind)
    | exact superpose eq75033 eq24
    | exact resolve eq24 eq75033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75044 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq762
       have i₂ := eq75033
       grind)
    | exact superpose eq75033 eq762
    | (have r₁ := eq762
       have r₂ := eq75033
       grind)
    | exact resolve eq762 eq75033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq75047 : (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq75044
  have eq75050 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq75037
    | exact resolve eq75037 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75037
  have eq75194 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75036 eq195
    | exact resolve eq195 eq75036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq75036
  have eq75264 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75033 eq75194
    | exact resolve eq75194 eq75033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75033 eq75194
  have eq75278 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75264 eq708
    | exact resolve eq708 eq75264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75352 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75264 eq75278
    | exact resolve eq75278 eq75264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75278
  have eq75373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75352 eq1533
    | (have j0 := eq1533 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1533 eq75352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75352
  have eq75376 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq75373
  have eq75377 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq75376
  have eq75385 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq75377
    | exact resolve eq75377 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75377
  have eq75391 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75050 eq75385
    | exact resolve eq75385 eq75050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75385
  have eq75427 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75391 eq184
    | exact resolve eq184 eq75391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq75467 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq75391 eq177
    | exact resolve eq177 eq75391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq75473 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq75391 eq190
    | exact resolve eq190 eq75391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq75391
  have eq80293 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq75047
       grind)
    | exact superpose eq75047 eq187
    | exact resolve eq187 eq75047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75047
  have eq80434 : x = (M.op x y) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75264 eq80293
    | exact resolve eq80293 eq75264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75264 eq80293
  have eq80435 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq80434
  have eq80442 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq80435 eq37
    | exact resolve eq37 eq80435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq80435
  have eq80459 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq80442
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq80442
    | exact resolve eq80442 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80442
  have eq80462 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75050 eq80459
    | exact resolve eq80459 eq75050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80459
  have eq80477 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq80462 eq785
    | exact resolve eq785 eq80462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq80462
  have eq80496 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28142 eq80477
    | exact resolve eq80477 eq28142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80477
  have eq80497 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq80496
  have eq80544 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80497 eq188
    | exact resolve eq188 eq80497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq80563 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80497 eq708
    | exact resolve eq708 eq80497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80497
  have eq80689 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq80563
    | exact resolve eq80563 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80563
  have eq80715 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80544 eq75467
    | exact resolve eq75467 eq80544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75467 eq80544
  have eq80794 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq80715
  have eq80806 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28142 eq80794
    | exact resolve eq80794 eq28142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80794
  have eq80807 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq80806
  have eq81037 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80807 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq80807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81038 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80807 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq80807
       grind)
    | exact resolve eq12 eq80807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80807
  have eq81141 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80689 eq81038
    | exact resolve eq81038 eq80689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81038
  have eq81142 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81141
  have eq81143 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80689 eq81037
    | exact resolve eq81037 eq80689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80689 eq81037
  have eq81144 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81143
  have eq81149 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq81144
       have r₂ := eq81142
       grind)
    | exact resolve eq81144 eq81142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81142 eq81144
  have eq81314 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81149 eq75473
    | exact resolve eq75473 eq81149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75473 eq81149
  have eq81403 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81314
  have eq81449 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq81403
    | exact resolve eq81403 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81403
  have eq81450 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81449
  have eq81461 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28142 eq81450
    | exact resolve eq81450 eq28142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28142 eq81450
  have eq81462 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81461
  have eq81464 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81462 eq27
    | exact resolve eq27 eq81462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81462
  have eq81485 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75050 eq81464
    | (have r₁ := eq81464
       have r₂ := eq75050
       grind)
    | exact resolve eq81464 eq75050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81464
  have eq81488 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq81485
  have eq81489 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq81488
  have eq81500 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq81489 eq27
    | exact resolve eq27 eq81489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81542 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq81489 eq75427
    | exact resolve eq75427 eq81489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75427
  have eq81543 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq81542
  have eq81563 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq81543
    | exact resolve eq81543 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81543
  have eq81568 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq81489 eq81563
    | exact resolve eq81563 eq81489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81489 eq81563
  have eq81572 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75050 eq81500
    | exact resolve eq81500 eq75050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75050 eq81500
  have eq81576 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq81572
  have eq81577 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq81576
       have r₂ := eq81568
       grind)
    | exact resolve eq81576 eq81568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81568 eq81576
  have eq81578 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq81577
       grind)
    | exact superpose eq81577 eq18
    | exact resolve eq18 eq81577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82022 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq81578 eq47383
    | exact resolve eq47383 eq81578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47383 eq81578
  have eq82129 : y = (M.op x y) ∨ x = y := by grind
  clear eq82022
  have eq82155 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq82129
  have eq82157 : x = y := by
    first
    | (have r₁ := eq82155
       have r₂ := eq81577
       grind)
    | exact resolve eq82155 eq81577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81577 eq82155
  have eq82165 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq82157
       grind)
    | exact superpose eq82157 eq18
    | exact resolve eq18 eq82157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82166 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq82157
       grind)
    | exact superpose eq82157 eq24
    | exact resolve eq24 eq82157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq82285 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8016
       have i₂ := eq82157
       grind)
    | exact superpose eq82157 eq8016
    | (have r₁ := eq8016
       have r₂ := eq82157
       grind)
    | exact resolve eq8016 eq82157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8016
  have eq82390 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq82285
  have eq82391 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq82390
  have eq82451 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq838 x
       grind)
    | (have r₁ := eq82391
       have r₂ := eq838 x
       grind)
    | exact resolve eq82391 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq82391
  have eq82505 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq82166
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq82166
    | exact resolve eq82166 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82166
  have eq82510 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82451
       have i₂ := eq82165
       grind)
    | exact superpose eq82165 eq82451
    | exact resolve eq82451 eq82165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82451
  have eq82511 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq82510
  have eq82526 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82505 eq82511
    | exact resolve eq82511 eq82505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82511
  have eq82535 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq82505 eq26
    | exact resolve eq26 eq82505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq82560 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq82505 eq1190
    | exact resolve eq1190 eq82505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq82505
  have eq82780 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82560
       have i₂ := eq82157
       grind)
    | exact superpose eq82157 eq82560
    | exact resolve eq82560 eq82157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82560
  have eq82804 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq82780
       have i₂ := eq82165
       grind)
    | exact superpose eq82165 eq82780
    | exact resolve eq82780 eq82165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82780
  have eq82805 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq82804
       have i₂ := eq82157
       grind)
    | exact superpose eq82157 eq82804
    | exact resolve eq82804 eq82157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82157 eq82804
  have eq82806 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq82805
  have eq82864 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq82165
       grind)
    | exact superpose eq82165 eq187
    | exact resolve eq187 eq82165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq82887 : (k x (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq708 x
       have i₂ := eq82165
       grind)
    | exact superpose eq82165 eq708
    | exact resolve eq708 eq82165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq82165
  have eq83090 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq82535 eq182
    | exact resolve eq182 eq82535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq83554 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82526 eq27
    | exact resolve eq27 eq82526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85063 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82526 eq83090
    | exact resolve eq83090 eq82526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83090
  have eq85162 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82535 eq85063
    | exact resolve eq85063 eq82535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85063
  have eq85172 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82526 eq85162
    | exact resolve eq85162 eq82526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82526 eq85162
  have eq86736 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85172 eq82806
    | exact resolve eq82806 eq85172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82806 eq85172
  have eq86762 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq86736
  have eq86781 : x = (M.op x y) := by
    first
    | (have r₁ := eq86762
       have r₂ := eq83554
       grind)
    | exact resolve eq86762 eq83554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83554 eq86762
  have eq86790 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq86781
       grind)
    | exact superpose eq86781 eq22
    | exact resolve eq22 eq86781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq87073 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq82887
       have i₂ := eq86781
       grind)
    | exact superpose eq86781 eq82887
    | exact resolve eq82887 eq86781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82887
  have eq87121 : x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq82864 eq87073
    | exact resolve eq87073 eq82864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82864 eq87073
  have eq87259 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq87121
       have i₂ := eq86781
       grind)
    | exact superpose eq86781 eq87121
    | exact resolve eq87121 eq86781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86781 eq87121
  have eq87342 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq86790 eq20
    | exact resolve eq20 eq86790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86790
  have eq87828 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq87259 eq1533
    | (have j0 := eq1533 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1533 eq87259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533 eq87259
  have eq87831 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq87828
  have eq87832 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq87831
  have eq87842 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq87832
    | exact resolve eq87832 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq87832
  have eq87848 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq87342 eq87842
    | exact resolve eq87842 eq87342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87842
  have eq87874 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87848 eq82535
    | exact resolve eq82535 eq87848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82535 eq87848
  have eq88004 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq87874 eq27
    | exact resolve eq27 eq87874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq87874
  have eq88082 : False := by grind
  exact eq88082

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq63 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq105 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq139 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq443 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq105
  have eq445 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq443 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq443
    | (have j0 := eq443 X0
       grind)
    | exact resolve eq443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq446 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq453 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq446 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq446
    | exact resolve eq446 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ X0) (σ X0)
       have i₂ := eq446 X0
       grind)
    | exact superpose eq446 eq63
    | exact resolve eq63 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq453 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq453
    | exact resolve eq453 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq453
  have eq474 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq473 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq473
    | exact resolve eq473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq581 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq459 (k X0 X0) (M.op x (σ X0))
       have i₂ := eq459 X0 x
       grind)
    | exact superpose eq459 eq459
    | exact resolve eq459 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq607 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq581 X0
       have i₂ := eq474 (k X0 X0)
       grind)
    | exact superpose eq474 eq581
    | exact resolve eq581 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq615 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq607 X0
       have i₂ := eq474 X0
       grind)
    | exact superpose eq474 eq607
    | exact resolve eq607 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq621 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq615 X0
       have i₂ := eq63 X0 X0 X0
       grind)
    | (have i₁ := eq615 X0
       have i₂ := eq63 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq63 eq615
    | exact resolve eq615 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq615
  have eq633 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq644 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq633 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq633
    | exact resolve eq633 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq648 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq644
  have eq706 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq137 x y
       grind)
    | exact superpose eq137 eq16
    | (have j1 := eq137 x y
       grind)
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq728 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq706
       have i₂ := eq446 y
       grind)
    | exact superpose eq446 eq706
    | exact resolve eq706 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq706
  have eq739 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq728
       have i₂ := eq474 y
       grind)
    | exact superpose eq474 eq728
    | exact resolve eq728 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq728
  have eq6830 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139
    | exact resolve eq139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq6962 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6830 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6830
    | (have j0 := eq6830 X0 X1
       grind)
    | exact resolve eq6830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6830
  have eq19023 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq739
       have i₂ := eq6962 x y
       grind)
    | exact superpose eq6962 eq739
    | (have j1 := eq6962 x y
       grind)
    | (have r₁ := eq739
       have r₂ := eq6962 x y
       grind)
    | (have r₁ := eq739
       have r₂ := eq6962 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq739
       have r₂ := eq6962 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq739 eq6962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq6962
  have eq19024 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq19023
  have eq19026 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19024
       grind)
    | exact superpose eq19024 eq16
    | exact resolve eq16 eq19024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19024
  have eq19027 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19026
       have r₂ := eq621 x
       grind)
    | exact resolve eq19026 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19026
  have eq19029 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19027
       grind)
    | exact superpose eq19027 eq10
    | exact resolve eq10 eq19027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19027
  have eq19138 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19029
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19029
    | exact resolve eq19029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19029
  have eq19163 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19138
       grind)
    | exact superpose eq19138 eq16
    | exact resolve eq16 eq19138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19138
  have eq19164 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq19163
       have r₂ := eq621 x
       grind)
    | exact resolve eq19163 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq19163
  have eq19183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq648 y
       have i₂ := eq19164
       grind)
    | exact superpose eq19164 eq648
    | exact resolve eq648 eq19164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19164
  have eq19269 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq19183
       have r₂ := eq16
       grind)
    | exact resolve eq19183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19183
  have eq19302 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq19269
       grind)
    | exact superpose eq19269 eq10
    | exact resolve eq10 eq19269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19269
  have eq19446 : x = (M.op y y) := by
    first
    | (have i₁ := eq19302
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19302
    | exact resolve eq19302 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19302
  have eq19514 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq648 y
       have i₂ := eq19446
       grind)
    | exact superpose eq19446 eq648
    | exact resolve eq648 eq19446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq19446
  have eq19600 : False := by grind
  exact eq19600

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_y_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq177 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq16 X0 x x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 X1 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X2 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq16 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X2 (k (M.op X0 X1) (M.op X0 X1))) = (M.op (k (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq13 eq182
    | (have j0 := eq182 X0 X1 X2
       have j1 := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq182 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq184 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq177 X2 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq184 eq177
    | exact resolve eq177 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq185 eq177
    | exact resolve eq177 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq188 eq177
    | exact resolve eq177 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq189 eq177
    | exact resolve eq177 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (τ X0) X1) X2
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq28 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X2 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 (M.op (k X0 X1) X2)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X1 X0 x
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq785 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X2 X0)) ∨ (k (M.op X0 X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X2 X0 X1
       have i₂ := eq28 (M.op X0 X1) (M.op X2 X0)
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 (M.op X0 X1) (M.op X2 X0)
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op X0 x)) ∨ x = (k (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq28 sF0 (M.op X0 x)
       grind)
    | exact superpose eq28 eq188
    | (have j1 := eq28 (M.op x y) (M.op X0 x)
       grind)
    | exact resolve eq188 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 X1) x) (M.op (M.op X0 X1) x)) ∨ x = (k (M.op x y) (M.op (M.op X0 X1) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1
       have i₂ := eq28 sF0 (M.op (M.op X0 X1) x)
       grind)
    | exact superpose eq28 eq179
    | (have j1 := eq28 (M.op x y) (M.op (M.op X0 X1) x)
       grind)
    | exact resolve eq179 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq798 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (k X0 (σ y))) ∨ (M.op (σ y) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq28 X0 sF3
       grind)
    | exact superpose eq28 eq185
    | (have j1 := eq28 X0 (σ y)
       grind)
    | exact resolve eq185 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq764 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq764 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq764 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq811 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq798
       grind)
    | exact superpose eq798 eq40
    | exact resolve eq40 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq811
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq811
    | exact resolve eq811 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq814 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq812
    | exact resolve eq812 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq818 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op x x)
       have i₂ := eq177 x x x
       grind)
    | exact superpose eq177 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 x (M.op x x)
       have r₂ := eq177 x x x
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X1 X1) x)) X1
       have r₂ := eq177 X0 (M.op X1 X1) x
       grind)
    | exact resolve eq12 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq819
    | (have j0 := eq819 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq819 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq821 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (k X1 (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq28 eq818
    | (have j0 := eq818 X0 X1
       have j1 := eq28 X0 X0
       grind)
    | (have r₁ := eq818 (k X0 X1) (M.op X1 X0)
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq818 (M.op X1 X0) (k X0 X1)
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq818 (M.op X1 X1) X0
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq818 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq829 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq808 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq808
    | (have j0 := eq808 (σ X0)
       grind)
    | exact resolve eq808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq814 eq803
    | exact resolve eq803 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq832
       have r₂ := eq27
       grind)
    | exact resolve eq832 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq843 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq839
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq839
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq839 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq839 eq189
    | exact resolve eq189 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq839 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq839 eq177
    | exact resolve eq177 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq839 eq191
    | exact resolve eq191 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq859 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq844 eq185
    | exact resolve eq185 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq889 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq859 eq850
    | exact resolve eq850 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq859
  have eq903 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq889
  have eq905 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq903
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq903
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq903 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq903 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq920 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq911 eq905
    | exact resolve eq905 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq911
  have eq1050 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq843 eq98
    | exact resolve eq98 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq1050
    | exact resolve eq1050 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1143 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1057 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1057
       grind)
    | exact resolve eq13 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1154 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq1143 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1207 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq809 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq809
    | (have j0 := eq809 (σ X0) X1
       grind)
    | exact resolve eq809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq820 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq820
    | (have j0 := eq820 (σ X0)
       grind)
    | exact resolve eq820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1223 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq843 eq820
    | (have j0 := eq820 (σ x)
       grind)
    | exact resolve eq820 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1231 : (σ (M.op x y)) = (k (σ (k (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq42 (k sF0 sF0)
       have i₂ := eq820 sF0
       grind)
    | exact superpose eq820 eq42
    | (have j1 := eq820 (M.op x y)
       grind)
    | exact resolve eq42 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1237 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1223
  have eq1242 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq42 eq1231
    | exact resolve eq1231 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1250 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq814 eq1237
    | exact resolve eq1237 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1255 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1217 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq1217
    | (have j0 := eq1217 X0
       grind)
    | exact resolve eq1217 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1260 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq1242
    | exact resolve eq1242 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1268 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1250 eq839
    | exact resolve eq839 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1272 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1250 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1250
       grind)
    | exact resolve eq13 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1277 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1250 eq178
    | exact resolve eq178 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq1283 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1286 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1268
  have eq2375 : ∀ X0 : G, (σ x) = (M.op (σ x) (k X0 (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1283 eq1277
    | exact resolve eq1277 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq2416 : (σ y) = (M.op (k (σ y) (σ x)) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1283 eq855
    | exact resolve eq855 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq1283
  have eq2418 : (σ y) = (M.op (k (σ y) (σ x)) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2416
  have eq2435 : ∀ X0 : G, (σ x) = (M.op (σ x) (k X0 (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq2375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2446 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq814 eq2418
    | exact resolve eq2418 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq2471 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1286 eq2446
    | exact resolve eq2446 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446
  have eq2525 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2471 eq177
    | exact resolve eq177 eq2471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq2880 : (τ (σ x)) = (k y y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq920 eq116
    | exact resolve eq116 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq2895 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq2880
    | exact resolve eq2880 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2880
  have eq2996 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq814 eq2435
    | exact resolve eq2435 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435
  have eq3023 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq2996
  have eq3159 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3023 eq2525
    | exact resolve eq2525 eq3023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525 eq3023
  have eq3187 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3159
  have eq3194 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq839 eq3187
    | exact resolve eq3187 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187
  have eq3196 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1286 eq3194
    | exact resolve eq3194 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3194
  have eq3197 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3196
  have eq3205 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq3197
       grind)
    | exact superpose eq3197 eq188
    | exact resolve eq188 eq3197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3211 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x
       have i₂ := eq3197
       grind)
    | exact superpose eq3197 eq177
    | exact resolve eq177 eq3197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3231 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3205 eq184
    | exact resolve eq184 eq3205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3235 : (M.op x y) = (M.op y y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3205 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq3205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3286 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3231 eq3211
    | exact resolve eq3211 eq3231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211 eq3231
  have eq3318 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3286
  have eq3612 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3318
       have i₂ := eq3235
       grind)
    | exact superpose eq3235 eq3318
    | exact resolve eq3318 eq3235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318
  have eq3618 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq3235
       grind)
    | exact superpose eq3235 eq184
    | exact resolve eq184 eq3235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3235
  have eq3648 : x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3612
  have eq4345 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x x) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq2895 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq2895
       grind)
    | exact resolve eq13 eq2895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895
  have eq4363 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x x) ∨ x = (k y y) := by
    intro X0
    first
    | (have j0 := eq4345 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4345
  have eq13020 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq1154 eq26
    | (have j1 := eq1154 (σ y)
       grind)
    | exact resolve eq26 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq13150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq814 eq13020
    | exact resolve eq13020 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13020
  have eq13176 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13150
       have r₂ := eq27
       grind)
    | exact resolve eq13150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13150
  have eq13196 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq13176
       grind)
    | exact superpose eq13176 eq40
    | exact resolve eq40 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13198 : x = (k y x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq820 x
       have i₂ := eq13176
       grind)
    | exact superpose eq13176 eq820
    | (have j0 := eq820 x
       grind)
    | exact resolve eq820 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13200 : x ≠ y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq808 x
       have i₂ := eq13176
       grind)
    | exact superpose eq13176 eq808
    | (have j0 := eq808 x
       grind)
    | exact resolve eq808 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13201 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq768 x x X0
       have i₂ := eq13176
       grind)
    | exact superpose eq13176 eq768
    | (have j0 := eq768 x x x
       grind)
    | exact resolve eq768 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13202 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq767 x x X0
       have i₂ := eq13176
       grind)
    | exact superpose eq13176 eq767
    | (have j0 := eq767 x x x
       grind)
    | exact resolve eq767 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13203 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq28 eq13202
    | (have j0 := eq13202 X0
       have j1 := eq28 x x
       grind)
    | exact resolve eq13202 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13202
  have eq13204 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq28 eq13201
    | (have j0 := eq13201 X0
       have j1 := eq28 x x
       grind)
    | exact resolve eq13201 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13201
  have eq13205 : x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq13198
       have r₂ := eq12 x x
       grind)
    | (have r₁ := eq13198
       have r₂ := eq12 y x
       grind)
    | exact resolve eq13198 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13198
  have eq13206 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13196
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13196
    | exact resolve eq13196 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13196
  have eq13208 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq13176 eq13203
    | (have j0 := eq13203 X0
       grind)
    | exact resolve eq13203 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13203
  have eq13209 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq13176 eq13204
    | (have j0 := eq13204 X0
       grind)
    | exact resolve eq13204 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13204
  have eq13210 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13206
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13206
    | exact resolve eq13206 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13206
  have eq13215 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq13205
       grind)
    | exact superpose eq13205 eq37
    | exact resolve eq37 eq13205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13217 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq768 y x X0
       have i₂ := eq13205
       grind)
    | exact superpose eq13205 eq768
    | (have j0 := eq768 y x x
       grind)
    | exact resolve eq768 eq13205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13218 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq767 y x X0
       have i₂ := eq13205
       grind)
    | exact superpose eq13205 eq767
    | (have j0 := eq767 y x x
       grind)
    | exact resolve eq767 eq13205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13205
  have eq13220 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (k x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq13218
    | (have j0 := eq13218 X0
       have j1 := eq28 x x
       grind)
    | exact resolve eq13218 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13218
  have eq13221 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ y = (k x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq13217
    | (have j0 := eq13217 X0
       have j1 := eq28 x x
       grind)
    | exact resolve eq13217 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13217
  have eq13223 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13215
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13215
    | exact resolve eq13215 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13215
  have eq13224 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (k x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13176 eq13220
    | (have j0 := eq13220 X0
       grind)
    | exact resolve eq13220 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13220
  have eq13225 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ y = (k x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13176 eq13221
    | (have j0 := eq13221 X0
       grind)
    | exact resolve eq13221 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13176 eq13221
  have eq13246 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13210 eq820
    | (have j0 := eq820 (σ x)
       grind)
    | exact resolve eq820 eq13210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13210
  have eq13260 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq13223 eq13246
    | exact resolve eq13246 eq13223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13246
  have eq13278 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq13223 eq768
    | (have j0 := eq768 (σ y) (σ x) x
       grind)
    | exact resolve eq768 eq13223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13279 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq13223 eq767
    | (have j0 := eq767 (σ y) (σ x) x
       grind)
    | exact resolve eq767 eq13223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq13223
  have eq13281 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq839 eq13279
    | (have j0 := eq13279 X0
       grind)
    | exact resolve eq13279 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13279
  have eq13282 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq839 eq13278
    | (have j0 := eq13278 X0
       grind)
    | exact resolve eq13278 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13278
  have eq13570 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq13260 eq108
    | exact resolve eq108 eq13260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13260
  have eq13582 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq13570
    | exact resolve eq13570 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13570
  have eq13683 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13582 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq13582
       grind)
    | exact resolve eq13 eq13582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13688 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13582 eq178
    | exact resolve eq178 eq13582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13582
  have eq13703 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq13683 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13683
  have eq14450 : y = (k x x) ∨ x = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq188 (M.op x x)
       have i₂ := eq13224 x
       grind)
    | exact superpose eq13224 eq188
    | exact resolve eq188 eq13224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14461 : x = (M.op x y) ∨ x = y ∨ y = (k x x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq13208 (M.op x x)
       have i₂ := eq13224 x
       grind)
    | exact superpose eq13224 eq13208
    | exact resolve eq13208 eq13224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13208 eq13224
  have eq14482 : x = (M.op x y) ∨ x = y ∨ y = (k x x) := by grind
  clear eq14461
  have eq14492 : y = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14482
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14482
    | exact resolve eq14482 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14482
  have eq15039 : x = (M.op y y) ∨ x = y ∨ y = (k x x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq13209 (M.op y x)
       have i₂ := eq13225 x
       grind)
    | exact superpose eq13225 eq13209
    | exact resolve eq13209 eq13225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13209
  have eq15060 : x = (M.op y y) ∨ x = y ∨ y = (k x x) := by grind
  clear eq15039
  have eq15070 : (M.op x y) = (M.op y y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq14492 eq15060
    | exact resolve eq15060 eq14492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15060
  have eq15095 : y = (M.op x (M.op x y)) ∨ y = (k x x) ∨ x = y ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq13225 y
       have i₂ := eq15070
       grind)
    | exact superpose eq15070 eq13225
    | exact resolve eq13225 eq15070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13225 eq15070
  have eq15130 : y = (M.op x (M.op x y)) ∨ y = (k x x) ∨ x = y := by grind
  clear eq15095
  have eq15135 : x = y ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq14450 eq15130
    | exact resolve eq15130 eq14450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14450 eq15130
  have eq15136 : y = (k x x) ∨ x = y := by grind
  clear eq15135
  have eq15148 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq15136
       grind)
    | exact superpose eq15136 eq40
    | exact resolve eq40 eq15136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15164 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq15148
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15148
    | exact resolve eq15148 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15148
  have eq15166 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq15164
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15164
    | exact resolve eq15164 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15164
  have eq15285 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq13281 eq13281
    | exact resolve eq13281 eq13281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15331 : ∀ X1 : G, (σ x) = (M.op (σ x) (M.op (σ x) X1)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq13281 eq177
    | exact resolve eq177 eq13281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13281
  have eq15353 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq15285
  have eq18773 : ∀ X0 : G, (σ x) = (k (M.op (σ x) X0) (σ x)) ∨ x = (k y x) ∨ x = y ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13703 eq13688
    | exact resolve eq13688 eq13703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13688
  have eq18923 : ∀ X0 : G, (σ x) = (k (M.op (σ x) X0) (σ x)) ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq18773 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18773
  have eq18976 : ∀ X0 : G, (σ x) = (k (k X0 (σ x)) (σ x)) ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13703 eq18923
    | exact resolve eq18923 eq13703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13703 eq18923
  have eq19700 : ∀ X1 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (k X1 (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) X1) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq15331 eq183
    | exact resolve eq183 eq15331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq15331
  have eq19732 : ∀ X1 : G, (k X1 (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) X1) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X1
    first
    | (have j0 := eq19700 X1
       grind)
    | (have r₁ := eq19700 X1
       have r₂ := eq15353
       grind)
    | exact resolve eq19700 eq15353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15353 eq19700
  have eq19742 : ∀ X1 : G, (M.op (σ y) X1) = (k X1 (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq15166 eq19732
    | exact resolve eq19732 eq15166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19732
  have eq20711 : ∀ X0 : G, (τ (σ x)) = (k (τ (k X0 (σ x))) x) ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq18976 eq142
    | exact resolve eq142 eq18976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18976
  have eq20744 : ∀ X0 : G, (τ (σ x)) = (k (k (τ X0) x) x) ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq142 eq20711
    | exact resolve eq20711 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20711
  have eq20757 : ∀ X0 : G, x = (k (k (τ X0) x) x) ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30 eq20744
    | exact resolve eq20744 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20744
  have eq21141 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq821 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq21173 : ∀ X0 : G, (σ y) = (M.op (σ x) (k X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq19742 eq13282
    | exact resolve eq13282 eq19742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13282 eq19742
  have eq21318 : ∀ X0 : G, (σ y) = (M.op (σ x) (k X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21173 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21173
  have eq33885 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X0 X0
       have i₂ := eq785 X0 X1 X0
       grind)
    | exact superpose eq785 eq177
    | (have j1 := eq785 X0 X1 X0
       grind)
    | exact resolve eq177 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35025 : x = (k (k x x) x) ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq20757
    | exact resolve eq20757 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20757
  have eq35041 : x = (k y x) ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq15136 eq35025
    | exact resolve eq35025 eq15136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35025
  have eq35042 : x = (k y x) ∨ x = y := by grind
  clear eq35041
  have eq35049 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq798
       have i₂ := eq35042
       grind)
    | exact superpose eq35042 eq798
    | exact resolve eq798 eq35042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq35051 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq35042
       grind)
    | exact superpose eq35042 eq37
    | exact resolve eq37 eq35042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35053 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq769 y x x
       have i₂ := eq35042
       grind)
    | exact superpose eq35042 eq769
    | (have j0 := eq769 y x x
       grind)
    | exact resolve eq769 eq35042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35042
  have eq35058 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq35051
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35051
    | exact resolve eq35051 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35051
  have eq38085 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq35053 (M.op x x)
       have i₂ := eq35053 x
       grind)
    | exact superpose eq35053 eq35053
    | exact resolve eq35053 eq35053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38090 : x = (M.op x (M.op x y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq35053 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35053
    | (have j0 := eq35053 y
       grind)
    | exact resolve eq35053 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35053
  have eq38161 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq38085
  have eq38181 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq35049 eq38090
    | exact resolve eq38090 eq35049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35049 eq38090
  have eq38183 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq38161
       have r₂ := eq13200
       grind)
    | exact resolve eq38161 eq13200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13200 eq38161
  have eq38246 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x
       have i₂ := eq38183
       grind)
    | exact superpose eq38183 eq177
    | exact resolve eq177 eq38183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38183
  have eq40787 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq38181 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq38181
       grind)
    | exact resolve eq13 eq38181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40820 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq40787 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40787
  have eq45274 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq40820 eq38181
    | exact resolve eq38181 eq40820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38181 eq40820
  have eq45450 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq45274
  have eq45526 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq45450 eq42
    | exact resolve eq42 eq45450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45532 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq45450 eq1207
    | (have j0 := eq1207 (M.op x y) X0
       grind)
    | exact resolve eq1207 eq45450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45450
  have eq45539 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq45532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45532
  have eq45550 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq45539
    | (have j0 := eq45539 X0
       grind)
    | exact resolve eq45539 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45539
  have eq45553 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq20 eq45526
    | exact resolve eq45526 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45526
  have eq45557 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3197 eq45550
    | exact resolve eq45550 eq3197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45550
  have eq45559 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq3197 eq45553
    | exact resolve eq45553 eq3197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197 eq45553
  have eq45563 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15166 eq45559
    | exact resolve eq45559 eq15166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15166 eq45559
  have eq53146 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq45557 eq26
    | (have j1 := eq45557 (σ y)
       grind)
    | exact resolve eq26 eq45557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45557
  have eq53511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq814 eq53146
    | exact resolve eq53146 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53146
  have eq53570 : y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq53511
       have r₂ := eq27
       grind)
    | exact resolve eq53511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53511
  have eq53616 : x = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq53570
       grind)
    | exact superpose eq53570 eq188
    | exact resolve eq188 eq53570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53633 : x = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq38246 x
       have i₂ := eq53570
       grind)
    | exact superpose eq53570 eq38246
    | exact resolve eq38246 eq53570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38246
  have eq53690 : x = (M.op y y) ∨ x = y := by grind
  clear eq53633
  have eq53715 : y = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq53616 eq184
    | exact resolve eq184 eq53616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53743 : (M.op x y) = (M.op y y) ∨ x = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq53616 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq53616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53862 : x = (k y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq53690
       grind)
    | exact superpose eq53690 eq28
    | exact resolve eq28 eq53690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53902 : x = (k y y) ∨ x = y := by grind
  clear eq53862
  have eq54029 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq53902
       grind)
    | exact superpose eq53902 eq41
    | exact resolve eq41 eq53902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54039 : y = (k x y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq820 y
       have i₂ := eq53902
       grind)
    | exact superpose eq53902 eq820
    | (have j0 := eq820 y
       grind)
    | exact resolve eq820 eq53902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54064 : y = (k x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq53690 eq54039
    | exact resolve eq54039 eq53690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54039
  have eq54065 : y = (k x y) ∨ x = y := by grind
  clear eq54064
  have eq54066 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq54029
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54029
    | exact resolve eq54029 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54029
  have eq54072 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq54066
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54066
    | exact resolve eq54066 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54066
  have eq54083 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq54065
       grind)
    | exact superpose eq54065 eq36
    | exact resolve eq36 eq54065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54065
  have eq54095 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq54083
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54083
    | exact resolve eq54083 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54083
  have eq54103 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq54072 eq21318
    | exact resolve eq21318 eq54072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21318 eq54072
  have eq54120 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq54103
  have eq54216 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq54120 eq189
    | exact resolve eq189 eq54120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54246 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq54120 eq177
    | exact resolve eq177 eq54120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54247 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq54120 eq178
    | exact resolve eq178 eq54120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54120
  have eq54336 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq54216 eq185
    | exact resolve eq185 eq54216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54216
  have eq58515 : x = (M.op x y) ∨ x = y ∨ x = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq53690
       have i₂ := eq53743
       grind)
    | exact superpose eq53743 eq53690
    | exact resolve eq53690 eq53743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58516 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq53743
       grind)
    | exact superpose eq53743 eq184
    | exact resolve eq184 eq53743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53743
  have eq58630 : x = (k (M.op x y) y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq58515
  have eq85293 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (k y y) := by
    first
    | exact superpose eq4363 eq26
    | (have j1 := eq4363 (σ y)
       grind)
    | exact resolve eq26 eq4363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363
  have eq85582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (k y y) := by
    first
    | exact superpose eq814 eq85293
    | exact resolve eq85293 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85293
  have eq85629 : y = (M.op x x) ∨ x = (k y y) := by
    first
    | (have r₁ := eq85582
       have r₂ := eq27
       grind)
    | exact resolve eq85582 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85582
  have eq85658 : y = (M.op x x) ∨ x = (k x x) := by
    first
    | exact superpose eq53570 eq85629
    | exact resolve eq85629 eq53570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53570 eq85629
  have eq85698 : x = (k x x) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq85658
       grind)
    | exact superpose eq85658 eq188
    | exact resolve eq188 eq85658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85728 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x
       have i₂ := eq85658
       grind)
    | exact superpose eq85658 eq177
    | exact resolve eq177 eq85658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85736 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq191 x x x
       have i₂ := eq85658
       grind)
    | exact superpose eq85658 eq191
    | exact resolve eq191 eq85658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85834 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq85698
       grind)
    | exact superpose eq85698 eq40
    | exact resolve eq40 eq85698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85847 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq809 x X0
       have i₂ := eq85698
       grind)
    | exact superpose eq85698 eq809
    | (have j0 := eq809 x X0
       grind)
    | (have r₁ := eq809 x x
       have r₂ := eq85698
       grind)
    | exact resolve eq809 eq85698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85851 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1207 x X0
       have i₂ := eq85698
       grind)
    | exact superpose eq85698 eq1207
    | (have j0 := eq1207 x X0
       grind)
    | exact resolve eq1207 eq85698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85858 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq85851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85851
  have eq85860 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq85847 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85847
  have eq85898 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq85858 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85858
    | (have j0 := eq85858 X0
       grind)
    | exact resolve eq85858 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85858
  have eq85900 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq85834
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85834
    | exact resolve eq85834 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85834
  have eq86207 : ∀ X0 : G, (σ (σ x)) ≠ (σ (σ x)) ∨ (k X0 (σ (σ x))) = (M.op (σ (σ x)) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq85900 eq1207
    | (have j0 := eq1207 (σ x) X0
       grind)
    | exact resolve eq1207 eq85900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85900
  have eq86214 : ∀ X0 : G, (k X0 (σ (σ x))) = (M.op (σ (σ x)) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq86207 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86207
  have eq86411 : x = (M.op y y) ∨ x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq85728 x
       have i₂ := eq85658
       grind)
    | exact superpose eq85658 eq85728
    | exact resolve eq85728 eq85658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85658 eq85728
  have eq86524 : x = (k x x) ∨ x = (M.op y y) := by grind
  clear eq86411
  have eq86598 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq809 x X0
       have i₂ := eq86524
       grind)
    | exact superpose eq86524 eq809
    | (have j0 := eq809 x X0
       grind)
    | (have r₁ := eq809 x x
       have r₂ := eq86524
       grind)
    | exact resolve eq809 eq86524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq86611 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq86598 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86598
  have eq87598 : (M.op x y) = (M.op y y) ∨ x = (k (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq790 x y
       have i₂ := eq85736 x
       grind)
    | exact superpose eq85736 eq790
    | exact resolve eq790 eq85736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq85736
  have eq87824 : (M.op x y) = (k y x) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq85860 y
       grind)
    | exact superpose eq85860 eq18
    | (have j1 := eq85860 y
       grind)
    | exact resolve eq18 eq85860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87883 : x = (M.op (k x x) (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq85860 x
       grind)
    | exact superpose eq85860 eq188
    | exact resolve eq188 eq85860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85860
  have eq87999 : x = (M.op y (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq85698 eq87883
    | exact resolve eq87883 eq85698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87883
  have eq88007 : (M.op x y) = (k x x) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq53616 eq87824
    | exact resolve eq87824 eq53616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87824
  have eq88159 : y = (M.op (M.op x y) x) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq87999 eq184
    | exact resolve eq184 eq87999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87999
  have eq88300 : x = (M.op x y) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq85698
       have i₂ := eq88007
       grind)
    | exact superpose eq88007 eq85698
    | exact resolve eq85698 eq88007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88007
  have eq88340 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq88300
  have eq88379 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88340 eq184
    | exact resolve eq184 eq88340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88415 : x = (k (M.op x y) y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88340 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq88340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88416 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq88340 eq177
    | exact resolve eq177 eq88340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88418 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq88340 eq178
    | exact resolve eq178 eq88340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88466 : (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58630 eq88415
    | exact resolve eq88415 eq58630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58630 eq88415
  have eq88515 : y = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88379 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq88379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88608 : y = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq88159 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq88159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88159
  have eq88650 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (k x (M.op x y)) := by
    first
    | exact superpose eq88515 eq88608
    | exact resolve eq88608 eq88515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88608
  have eq89160 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq85898 eq212
    | exact resolve eq212 eq85898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq89215 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq85898 eq26
    | (have j1 := eq85898 (σ y)
       grind)
    | exact resolve eq26 eq85898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85898
  have eq89461 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq89215 eq115
    | exact resolve eq115 eq89215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq89215
  have eq89507 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq53616 eq89461
    | exact resolve eq89461 eq53616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53616 eq89461
  have eq89512 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq85698 eq89507
    | exact resolve eq89507 eq85698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85698 eq89507
  have eq89516 : x = (M.op y (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq88340 eq89512
    | exact resolve eq89512 eq88340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89512
  have eq90888 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq86611 y
       grind)
    | exact superpose eq86611 eq18
    | (have j1 := eq86611 y
       grind)
    | exact resolve eq18 eq86611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86611
  have eq91076 : (M.op x y) = (k x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq53690 eq90888
    | exact resolve eq90888 eq53690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53690 eq90888
  have eq91297 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86524
       have i₂ := eq91076
       grind)
    | exact superpose eq91076 eq86524
    | exact resolve eq86524 eq91076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86524 eq91076
  have eq91332 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq91297
  have eq91441 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88416 y
       have i₂ := eq91332
       grind)
    | exact superpose eq91332 eq88416
    | exact resolve eq88416 eq91332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88416 eq91332
  have eq91493 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq91441
  have eq93900 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k (τ (M.op (M.op (σ x) (σ y)) X0)) x) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq89160 eq142
    | exact resolve eq142 eq89160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93934 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k (τ (M.op (M.op (σ x) (σ y)) X0)) (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq88340 eq93900
    | exact resolve eq93900 eq88340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88340 eq93900
  have eq93935 : ∀ X0 : G, (M.op x y) = (k (τ (M.op (M.op (σ x) (σ y)) X0)) (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq89516 eq93934
    | exact resolve eq93934 eq89516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89516 eq93934
  have eq99363 : ∀ X0 X1 : G, (σ (k (M.op x y) X1)) = (k (k (M.op (M.op (σ x) (σ y)) X0) (σ (M.op x y))) (σ X1)) ∨ x = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq93935 eq448
    | exact resolve eq448 eq93935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq99364 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq93935 eq35
    | exact resolve eq35 eq93935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq93935
  have eq99382 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq99364
    | (have j0 := eq99364 X0
       grind)
    | exact resolve eq99364 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99364
  have eq99383 : ∀ X0 X1 : G, (σ (k (M.op x y) X1)) = (k (k (M.op (M.op (σ x) (σ y)) X0) (σ (M.op x y))) (σ X1)) ∨ x = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq99363
    | (have j0 := eq99363 X0 X1
       grind)
    | exact resolve eq99363 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99363
  have eq99393 : ∀ X0 : G, (σ x) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3205 eq99382
    | exact resolve eq99382 eq3205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99382
  have eq99394 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ X1)) = (k (k (M.op (M.op (σ x) (σ y)) X0) (σ (M.op x y))) (σ X1)) ∨ x = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq38 eq99383
    | exact resolve eq99383 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99383
  have eq99402 : ∀ X0 X1 : G, (k (σ x) (σ X1)) = (k (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) (σ X1)) ∨ x = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq3205 eq99394
    | exact resolve eq99394 eq3205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205 eq99394
  have eq99406 : ∀ X1 : G, (k (σ x) (σ X1)) = (k (M.op (σ x) (σ y)) (σ X1)) ∨ x = (M.op y (M.op x y)) := by
    intro X1
    first
    | exact superpose eq89160 eq99402
    | exact resolve eq99402 eq89160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99402
  have eq99408 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq185 eq99393
    | exact resolve eq99393 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99440 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq99393 eq89160
    | exact resolve eq89160 eq99393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89160 eq99393
  have eq99479 : x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq99440
  have eq99493 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq35058 eq99408
    | exact resolve eq99408 eq35058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99408
  have eq99712 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq99493 eq803
    | exact resolve eq803 eq99493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99493
  have eq100390 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91493
       have i₂ := eq88466
       grind)
    | exact superpose eq88466 eq91493
    | exact resolve eq91493 eq88466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100460 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq88466
       grind)
    | exact superpose eq88466 eq28
    | exact resolve eq28 eq88466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88466
  have eq100508 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by grind
  clear eq100460
  have eq100530 : x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq100390
  have eq103965 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq100508
       grind)
    | exact superpose eq100508 eq40
    | exact resolve eq40 eq100508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104021 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have i₁ := eq103965
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq103965
    | exact resolve eq103965 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103965
  have eq104029 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq20 eq104021
    | exact resolve eq104021 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104021
  have eq104035 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq3648 eq104029
    | exact resolve eq104029 eq3648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3648 eq104029
  have eq104569 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq99712 eq189
    | exact resolve eq189 eq99712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99712
  have eq104965 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq104035 eq142
    | exact resolve eq142 eq104035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq104035
  have eq105037 : x = (k x x) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq30 eq104965
    | exact resolve eq104965 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104965
  have eq105041 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq100508 eq105037
    | exact resolve eq105037 eq100508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100508 eq105037
  have eq105042 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq105041
  have eq105052 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105042 eq41
    | exact resolve eq41 eq105042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105090 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq105052
    | exact resolve eq105052 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105052
  have eq105092 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105090
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq105090
    | exact resolve eq105090 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105090
  have eq105117 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq105092 eq768
    | (have j0 := eq768 (σ (M.op x y)) (σ y) x
       grind)
    | exact resolve eq768 eq105092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105092
  have eq108195 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ (σ x))) (σ y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq86214 eq201
    | exact resolve eq201 eq86214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq86214
  have eq108202 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ (σ x))) (σ y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq99406 eq108195
    | exact resolve eq108195 eq99406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99406 eq108195
  have eq108227 : (σ x) = (M.op (k (σ x) (σ (σ x))) (σ y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq99479 eq108202
    | exact resolve eq108202 eq99479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99479 eq108202
  have eq108356 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq108227 eq177
    | exact resolve eq177 eq108227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108227
  have eq108407 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ x = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq54247 eq108356
    | (have j0 := eq108356 X0
       have j1 := eq54247 X0
       grind)
    | exact resolve eq108356 eq54247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108356
  have eq122033 : (M.op x y) = (k y y) ∨ x = (k (M.op x y) y) ∨ x = (k x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq87598
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq87598
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq87598 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122057 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq87598
       grind)
    | exact superpose eq87598 eq184
    | exact resolve eq184 eq87598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122123 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq87598
       grind)
    | exact superpose eq87598 eq28
    | exact resolve eq28 eq87598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87598
  have eq122210 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq100530 eq122123
    | exact resolve eq122123 eq100530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122123
  have eq122223 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq105042 eq122057
    | exact resolve eq122057 eq105042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122057
  have eq122224 : (M.op x y) = (k y y) ∨ x = (k (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq105042 eq122033
    | exact resolve eq122033 eq105042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122033
  have eq122230 : (M.op x y) = (k y y) ∨ x = (k (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq122210 eq122224
    | exact resolve eq122224 eq122210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122210 eq122224
  have eq122233 : (M.op x y) = (k y y) ∨ x = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq808 (M.op x y)
       grind)
    | (have r₁ := eq122230
       have r₂ := eq808 (M.op x y)
       grind)
    | exact resolve eq122230 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122230
  have eq122636 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq122223 eq829
    | (have j0 := eq829 (M.op x y)
       grind)
    | exact resolve eq829 eq122223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122223
  have eq122645 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq122636
  have eq122655 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq122645
    | exact resolve eq122645 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122645
  have eq122663 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k (M.op x y) y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3618 eq122655
    | exact resolve eq122655 eq3618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3618 eq122655
  have eq122728 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq122233
       grind)
    | exact superpose eq122233 eq41
    | exact resolve eq41 eq122233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122233
  have eq122786 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq122728
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq122728
    | exact resolve eq122728 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122728
  have eq122796 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq122786
    | exact resolve eq122786 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122786
  have eq124937 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k (M.op x y) y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq122663 eq839
    | exact resolve eq839 eq122663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq122663
  have eq125129 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k (M.op x y) x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq45563 eq124937
    | exact resolve eq124937 eq45563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124937
  have eq125141 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq45563 eq125129
    | exact resolve eq125129 eq45563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45563 eq125129
  have eq125149 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq91493 eq125141
    | exact resolve eq125141 eq91493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125141
  have eq125152 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq91493 eq125149
    | exact resolve eq125149 eq91493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91493 eq125149
  have eq125155 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq808 (M.op x y)
       grind)
    | (have r₁ := eq125152
       have r₂ := eq808 (M.op x y)
       grind)
    | exact resolve eq125152 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125152
  have eq125206 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq125155 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq125155
       grind)
    | exact resolve eq13 eq125155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125269 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq125206 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125206
  have eq126104 : y = (M.op x y) ∨ x = y ∨ y = (k x (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq58516 eq88650
    | exact resolve eq88650 eq58516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58516
  have eq126209 : x ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (k x (M.op x y)) := by grind
  clear eq88650
  have eq126214 : y = (M.op x y) ∨ x = y ∨ y = (k x (M.op x y)) ∨ x = (k (M.op x y) y) := by grind
  clear eq126104
  have eq126218 : y = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq126209
       have r₂ := eq88515
       grind)
    | exact resolve eq126209 eq88515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88515 eq126209
  have eq126235 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k x (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq100530 eq126214
    | exact resolve eq126214 eq100530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126214
  have eq126236 : y = (M.op x y) ∨ y = (k x (M.op x y)) ∨ x = (k (M.op x y) y) := by grind
  clear eq126235
  have eq126243 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq100530 eq126236
    | exact resolve eq126236 eq100530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100530 eq126236
  have eq126269 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq126218 eq768
    | (have j0 := eq768 x (M.op x y) x
       grind)
    | exact resolve eq768 eq126218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126218
  have eq126272 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq126269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126269
  have eq126278 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq88418 eq126272
    | (have j0 := eq126272 X0
       have j1 := eq88418 X0
       grind)
    | exact resolve eq126272 eq88418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88418 eq126272
  have eq126406 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq184 (M.op x x)
       have i₂ := eq126278 x
       grind)
    | exact superpose eq126278 eq184
    | exact resolve eq184 eq126278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126278
  have eq126562 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq126406 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq126406
       grind)
    | exact resolve eq13 eq126406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126622 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq126562 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126562
  have eq127342 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq126622 eq126406
    | exact resolve eq126406 eq126622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126406
  have eq127542 : y ≠ (k x (M.op x y)) ∨ y = (M.op (M.op x y) x) := by grind
  clear eq126622
  have eq127544 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) := by grind
  clear eq127342
  have eq127549 : x ≠ (k x (M.op x y)) ∨ y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq53715 eq127542
    | exact resolve eq127542 eq53715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53715 eq127542
  have eq127586 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq88379 eq127549
    | exact resolve eq127549 eq88379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88379 eq127549
  have eq127609 : y = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq127586
       have r₂ := eq127544
       grind)
    | exact resolve eq127586 eq127544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127544 eq127586
  have eq127649 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq127609 eq188
    | exact resolve eq188 eq127609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127684 : ∀ X0 : G, x = (M.op y (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq127609 eq177
    | exact resolve eq177 eq127609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127691 : ∀ X0 : G, y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | exact superpose eq127609 eq191
    | exact resolve eq191 eq127609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127803 : (M.op x y) = (M.op y y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq127649 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq127649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127649
  have eq128014 : ∀ X1 : G, x = (M.op (M.op X1 y) (M.op X1 y)) ∨ y = (k x (M.op X1 y)) := by
    intro X1
    first
    | (have i₁ := eq785 y (M.op x x) x
       have i₂ := eq127684 x
       grind)
    | exact superpose eq127684 eq785
    | exact resolve eq785 eq127684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq129258 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq127803
       grind)
    | exact superpose eq127803 eq184
    | exact resolve eq184 eq127803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq127803
  have eq138582 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq125269 eq125155
    | exact resolve eq125155 eq125269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125155 eq125269
  have eq138827 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq138582
  have eq138945 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq138827 eq1207
    | (have j0 := eq1207 (M.op x y) X0
       grind)
    | exact resolve eq1207 eq138827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207 eq138827
  have eq138952 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq138945 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138945
  have eq138970 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq138952
    | (have j0 := eq138952 X0
       grind)
    | exact resolve eq138952 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138952
  have eq138977 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1286 eq138970
    | exact resolve eq138970 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286 eq138970
  have eq138983 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq138977 X0
       have j1 := eq846 X0
       grind)
    | (have r₁ := eq138977 X0
       have r₂ := eq846 X0
       grind)
    | exact resolve eq138977 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq138977
  have eq140512 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq138983 eq26
    | (have j1 := eq138983 (σ y)
       grind)
    | exact resolve eq26 eq138983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138983
  have eq140832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq814 eq140512
    | exact resolve eq140512 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq140512
  have eq140862 : y = (M.op x x) := by
    first
    | (have r₁ := eq140832
       have r₂ := eq27
       grind)
    | exact resolve eq140832 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140832
  have eq140913 : x = (M.op y y) := by
    first
    | (have i₁ := eq127684 x
       have i₂ := eq140862
       grind)
    | exact superpose eq140862 eq127684
    | exact resolve eq127684 eq140862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127684
  have eq140954 : ∀ X0 : G, x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x
       have i₂ := eq140862
       grind)
    | exact superpose eq140862 eq177
    | exact resolve eq177 eq140862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141375 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 x)) ∨ x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq28 y (M.op X0 x)
       have i₂ := eq140954 X0
       grind)
    | exact superpose eq140954 eq28
    | (have j0 := eq28 y (M.op X0 x)
       grind)
    | exact resolve eq28 eq140954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158913 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f158913_14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = X1 := by
      intro X0 X1 X2
      grind
    have f158913_15 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f158913_24 : (σ x) ≠ (M.op (M.op X0 (σ x)) (σ (M.op x y))) := by grind
    have f158913_25 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by grind
    have f158913_26 : x ≠ (M.op x y) := by grind
    have f158913_29 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f158913_15 X0
         grind)
      | (have r₁ := f158913_15 X0
         have r₂ := f158913_25
         grind)
      | exact resolve f158913_15 f158913_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f158913_30 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
      intro X0
      first
      | (have j0 := f158913_29 X0
         grind)
      | (have r₁ := f158913_29 X0
         have r₂ := f158913_26
         grind)
      | exact resolve f158913_29 f158913_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f158913_117 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) := by
      intro X0
      first
      | (have i₁ := f158913_14 X0 (σ x) (M.op (σ (M.op x y)) x)
         have i₂ := f158913_30 x
         grind)
      | exact superpose f158913_30 f158913_14
      | exact resolve f158913_14 f158913_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f158913_149 : (σ x) ≠ (σ x) := by
      first
      | (have i₁ := f158913_24
         have i₂ := f158913_117 X0
         grind)
      | exact superpose f158913_117 f158913_24
      | (have r₁ := f158913_24
         have r₂ := f158913_117 X0
         grind)
      | exact resolve f158913_24 f158913_117
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f158913_156 : False := by grind
    exact f158913_156
  have eq183919 : ∀ X0 : G, x = (k y (M.op X0 x)) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq178 X0 x (M.op X0 x)
       have i₂ := eq141375 X0
       grind)
    | exact superpose eq141375 eq178
    | (have j1 := eq141375 X0
       grind)
    | exact resolve eq178 eq141375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183921 : ∀ X0 : G, x = (k y (M.op X0 x)) ∨ (M.op X0 x) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq191 x (M.op X0 x) X0
       have i₂ := eq141375 X0
       grind)
    | exact superpose eq141375 eq191
    | (have j1 := eq141375 X0
       grind)
    | exact resolve eq191 eq141375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141375
  have eq184094 : ∀ X0 : G, x = (k y y) ∨ y = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq183919 (M.op X0 y)
       have i₂ := eq127691 X0
       grind)
    | exact superpose eq127691 eq183919
    | exact resolve eq183919 eq127691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127691
  have eq184174 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183919 x
       have i₂ := eq140862
       grind)
    | exact superpose eq140862 eq183919
    | exact resolve eq183919 eq140862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183919
  have eq184260 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq184174
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq184174
    | exact resolve eq184174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184174
  have eq184286 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq53902 eq184094
    | exact resolve eq184094 eq53902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53902 eq184094
  have eq184339 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq184260
       grind)
    | exact superpose eq184260 eq41
    | exact resolve eq41 eq184260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184379 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1255 y
       have i₂ := eq184260
       grind)
    | exact superpose eq184260 eq1255
    | (have j0 := eq1255 y
       grind)
    | exact resolve eq1255 eq184260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq184260
  have eq184405 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq184379
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq184379
    | exact resolve eq184379 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184379
  have eq184411 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq184339
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq184339
    | exact resolve eq184339 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184339
  have eq184414 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq184405
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq184405
    | exact resolve eq184405 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184405
  have eq184417 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq184411
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq184411
    | exact resolve eq184411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184411
  have eq184420 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq184414
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq184414
    | exact resolve eq184414 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184414
  have eq184423 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq184420
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq184420
    | exact resolve eq184420 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184420
  have eq184424 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54095 eq184423
    | exact resolve eq184423 eq54095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54095 eq184423
  have eq184435 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq184417 eq805
    | (have j0 := eq805 (σ y)
       grind)
    | exact resolve eq805 eq184417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184459 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq184417 eq769
    | (have j0 := eq769 (σ y) (σ y) x
       grind)
    | exact resolve eq769 eq184417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184460 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq184417 eq768
    | (have j0 := eq768 (σ y) (σ y) x
       grind)
    | exact resolve eq768 eq184417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq184417
  have eq184467 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54247 eq184460
    | (have j0 := eq184460 X0
       have j1 := eq54247 X0
       grind)
    | exact resolve eq184460 eq54247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54247 eq184460
  have eq184468 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54246 eq184459
    | (have j0 := eq184459 X0
       have j1 := eq54246 X0
       grind)
    | exact resolve eq184459 eq54246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54246 eq184459
  have eq184471 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54336 eq184435
    | exact resolve eq184435 eq54336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54336 eq184435
  have eq184646 : x = (k y y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq188 (M.op x x)
       have i₂ := eq184286 x
       grind)
    | exact superpose eq184286 eq188
    | exact resolve eq188 eq184286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq184681 : x = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq140954 (M.op x x)
       have i₂ := eq184286 x
       grind)
    | exact superpose eq184286 eq140954
    | exact resolve eq140954 eq184286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140954 eq184286
  have eq184777 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq184681
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq184681
    | exact resolve eq184681 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184681
  have eq184872 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq184777
       grind)
    | exact superpose eq184777 eq41
    | exact resolve eq41 eq184777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184910 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq829 y
       have i₂ := eq184777
       grind)
    | exact superpose eq184777 eq829
    | (have j0 := eq829 y
       grind)
    | exact resolve eq829 eq184777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq184777
  have eq184948 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq184910
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq184910
    | exact resolve eq184910 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184910
  have eq184952 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq184872
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq184872
    | exact resolve eq184872 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184872
  have eq184957 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq184948
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq184948
    | exact resolve eq184948 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184948
  have eq184958 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq184952
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq184952
    | exact resolve eq184952 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184952
  have eq184963 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq184957
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq184957
    | exact resolve eq184957 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184957
  have eq185036 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq184646
       grind)
    | exact superpose eq184646 eq41
    | exact resolve eq41 eq184646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq184646
  have eq185098 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq185036
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq185036
    | exact resolve eq185036 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185036
  have eq185104 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq185098
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq185098
    | exact resolve eq185098 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185098
  have eq185110 : (σ x) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq184958 eq185104
    | exact resolve eq185104 eq184958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185104
  have eq185399 : (τ (σ x)) = (k y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq185110 eq116
    | exact resolve eq116 eq185110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq185402 : (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq185110 eq122796
    | exact resolve eq122796 eq185110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122796
  have eq185407 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq185110 eq805
    | (have j0 := eq805 (σ y)
       grind)
    | exact resolve eq805 eq185110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq185110
  have eq185436 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq185402
  have eq185443 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq185399
    | exact resolve eq185399 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185399
  have eq185510 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq185443 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq185443
       grind)
    | exact resolve eq13 eq185443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185443
  have eq185586 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k y y) := by
    intro X0
    first
    | (have j0 := eq185510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185510
  have eq186646 : y = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (k y y) := by
    first
    | exact superpose eq185586 eq129258
    | exact resolve eq129258 eq185586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129258 eq185586
  have eq186968 : y = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq126243 eq186646
    | exact resolve eq186646 eq126243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186646
  have eq187051 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq105042 eq186968
    | exact resolve eq186968 eq105042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105042 eq186968
  have eq189037 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184424 eq91
    | exact resolve eq91 eq184424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq184424
  have eq189055 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq189037
    | exact resolve eq189037 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189037
  have eq189069 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184471 eq189
    | exact resolve eq189 eq184471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184471
  have eq189346 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184958 eq21141
    | (have j0 := eq21141 (σ y)
       grind)
    | exact resolve eq21141 eq184958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21141
  have eq191182 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (k x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq189055 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq189055
       grind)
    | exact resolve eq13 eq189055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191261 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (k x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq191182 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191182
  have eq191589 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq189069 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq189069
       grind)
    | exact resolve eq13 eq189069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191668 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq191589 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191589
  have eq191819 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq189346 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq189346
       grind)
    | exact resolve eq13 eq189346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191830 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq189346 eq191
    | exact resolve eq191 eq189346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191898 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq191819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191819
  have eq192585 : ∀ X0 : G, (σ x) = (k (σ y) (σ (M.op X0 x))) ∨ (M.op X0 x) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 x)
       have i₂ := eq183921 X0
       grind)
    | exact superpose eq183921 eq37
    | (have j1 := eq183921 X0
       grind)
    | exact resolve eq37 eq183921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192607 : ∀ X0 : G, (σ x) = (k (σ y) (σ (M.op X0 x))) ∨ (M.op X0 x) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq192585 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq192585
    | (have j0 := eq192585 X0
       grind)
    | exact resolve eq192585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192585
  have eq204227 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184467 eq184468
    | exact resolve eq184468 eq184467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204351 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184468 eq184467
    | exact resolve eq184467 eq184468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184467
  have eq204390 : (σ y) = (k (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184468 eq33885
    | (have j0 := eq33885 (σ y) (σ y)
       grind)
    | exact resolve eq33885 eq184468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184468
  have eq204440 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq204351
  have eq204450 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq204227
  have eq204456 : (σ y) = (k (σ x) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq204390
       have r₂ := eq184963
       grind)
    | exact resolve eq204390 eq184963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184963 eq204390
  have eq204463 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq204450 eq204456
    | exact resolve eq204456 eq204450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204456
  have eq204572 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq204440 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq204440
       grind)
    | exact resolve eq13 eq204440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204583 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq204440 eq191
    | exact resolve eq191 eq204440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204440
  have eq204657 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq204572 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204572
  have eq204871 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq204450
  have eq204919 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq204463 eq98
    | exact resolve eq98 eq204463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204463
  have eq205015 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq204919
    | exact resolve eq204919 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204919
  have eq205552 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205015 eq185
    | exact resolve eq185 eq205015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq205601 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq205015 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq205015
       grind)
    | exact resolve eq13 eq205015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205686 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq205601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205601
  have eq206604 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq185407 eq189
    | exact resolve eq189 eq185407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq185407
  have eq208114 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191261 eq189055
    | exact resolve eq189055 eq191261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189055 eq191261
  have eq208456 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq208114
  have eq208573 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184958 eq208456
    | exact resolve eq208456 eq184958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208456
  have eq208655 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq208573
       grind)
    | exact superpose eq208573 eq36
    | exact resolve eq36 eq208573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq208573
  have eq208686 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq208655
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq208655
    | exact resolve eq208655 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208655
  have eq215388 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191668 eq189069
    | exact resolve eq189069 eq191668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189069
  have eq215740 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq215388
  have eq215839 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184958 eq215740
    | exact resolve eq215740 eq184958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215740
  have eq215943 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq215839 eq178
    | exact resolve eq178 eq215839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220260 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191898 eq189346
    | exact resolve eq189346 eq191898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189346
  have eq220482 : (M.op x y) = (M.op (k (M.op x y) (σ y)) y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191898 eq197
    | exact resolve eq197 eq191898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220570 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191898 eq191830
    | exact resolve eq191830 eq191898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191830 eq191898
  have eq220576 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq220570
  have eq220626 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq220260
  have eq220702 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184958 eq220576
    | exact resolve eq220576 eq184958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220576
  have eq220709 : (M.op x y) = (M.op (k (M.op x y) (σ y)) x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35058 eq220482
    | exact resolve eq220482 eq35058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220482
  have eq220763 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184958 eq220626
    | exact resolve eq220626 eq184958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220626
  have eq220799 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq220702
    | exact resolve eq220702 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220702
  have eq220841 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq220763 eq220799
    | exact resolve eq220799 eq220763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220763 eq220799
  have eq220958 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq220841 eq803
    | exact resolve eq803 eq220841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220841
  have eq221024 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq220958
  have eq222634 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq191 x (M.op X0 x) X0
       have i₂ := eq789 X0
       grind)
    | exact superpose eq789 eq191
    | (have j1 := eq789 X0
       grind)
    | exact resolve eq191 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq789
  have eq222727 : ∀ X0 : G, x = (k (M.op x y) (M.op X0 x)) ∨ y = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq127609 eq222634
    | (have j0 := eq222634 X0
       grind)
    | exact resolve eq222634 eq127609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222634
  have eq223410 : ∀ X0 : G, (σ x) = (k (σ (M.op x y)) (σ (M.op X0 x))) ∨ y = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq222727 eq38
    | (have j1 := eq222727 X0
       grind)
    | exact resolve eq38 eq222727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq223422 : ∀ X0 : G, (σ x) = (k (σ (M.op x y)) (σ (M.op X0 x))) ∨ y = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq223410 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq223410
    | (have j0 := eq223410 X0
       grind)
    | exact resolve eq223410 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223410
  have eq226417 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191668 eq204583
    | exact resolve eq204583 eq191668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191668 eq204583
  have eq226573 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq226417
  have eq226609 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq204657 eq226573
    | exact resolve eq226573 eq204657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204657 eq226573
  have eq226615 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq221024 eq226609
    | exact resolve eq226609 eq221024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226609
  have eq226617 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq184958 eq226615
    | exact resolve eq226615 eq184958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184958 eq226615
  have eq226618 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq226617
    | exact resolve eq226617 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226617
  have eq226619 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq221024 eq226618
    | exact resolve eq226618 eq221024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221024 eq226618
  have eq226620 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq208686 eq226619
    | exact resolve eq226619 eq208686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208686 eq226619
  have eq226621 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq226620
  have eq226724 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq226621 eq215943
    | exact resolve eq215943 eq226621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215943
  have eq226874 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq226724
  have eq226938 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq226874
       have r₂ := eq204871
       grind)
    | exact resolve eq226874 eq204871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204871 eq226874
  have eq226978 : (σ x) = (σ y) ∨ y = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq226938 eq205015
    | exact resolve eq205015 eq226938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205015
  have eq227055 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq226938 eq177
    | exact resolve eq177 eq226938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq227164 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq226978
  have eq227656 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205552 eq227055
    | exact resolve eq227055 eq205552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205552 eq227055
  have eq227812 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x x) := by grind
  clear eq227656
  have eq227851 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq227164 eq227812
    | exact resolve eq227812 eq227164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227812
  have eq233906 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq227851 eq158913
    | exact resolve eq158913 eq227851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158913 eq227851
  have eq234008 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (k x x) := by grind
  clear eq233906
  have eq234078 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq226938 eq234008
    | exact resolve eq234008 eq226938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234008
  have eq240703 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq206604 eq108407
    | exact resolve eq108407 eq206604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206604
  have eq240864 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq240703
    | exact resolve eq240703 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240703
  have eq240866 : (σ x) = (σ y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq104569 eq240864
    | exact resolve eq240864 eq104569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104569 eq240864
  have eq240867 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq215839 eq240866
    | exact resolve eq240866 eq215839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215839 eq240866
  have eq240868 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq240867
  have eq240903 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq240868 eq108407
    | exact resolve eq108407 eq240868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108407 eq240868
  have eq241011 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq226621 eq240903
    | exact resolve eq240903 eq226621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226621 eq240903
  have eq241012 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq241011
  have eq241321 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq241012 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq28 eq241012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq241012
  have eq241406 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq241321
  have eq241722 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq241406 eq98
    | exact resolve eq98 eq241406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq241406
  have eq241859 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq241722
    | exact resolve eq241722 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241722
  have eq243677 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ y = (k x x) := by
    first
    | exact superpose eq241859 eq197
    | exact resolve eq197 eq241859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241859
  have eq243800 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ y = (k x x) := by
    first
    | exact superpose eq15136 eq243677
    | exact resolve eq243677 eq15136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15136 eq243677
  have eq243811 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127609 eq243800
    | exact resolve eq243800 eq127609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127609 eq243800
  have eq251609 : y ≠ (M.op x y) ∨ x = (k (M.op x y) y) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq187051
  have eq251620 : y = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq251609
       have r₂ := eq126243
       grind)
    | exact resolve eq251609 eq126243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126243 eq251609
  have eq251656 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq251620 eq42
    | exact resolve eq42 eq251620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251620
  have eq251723 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq20 eq251656
    | exact resolve eq251656 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251656
  have eq251735 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) y) := by
    first
    | (have i₁ := eq251723
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq251723
    | exact resolve eq251723 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251723
  have eq251760 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq251735 eq1260
    | exact resolve eq1260 eq251735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq251735
  have eq251815 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq185436 eq251760
    | exact resolve eq251760 eq185436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185436 eq251760
  have eq251834 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq35058 eq251815
    | exact resolve eq251815 eq35058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251815
  have eq254443 : (M.op x y) = (M.op (k (M.op x y) (σ y)) y) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205686 eq197
    | exact resolve eq197 eq205686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205686
  have eq254726 : (M.op x y) = (M.op (k (M.op x y) (σ y)) x) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14492 eq254443
    | exact resolve eq254443 eq14492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254443
  have eq254835 : (M.op x y) = (M.op (k (M.op x y) (σ x)) x) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq227164 eq254726
    | exact resolve eq254726 eq227164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227164 eq254726
  have eq261595 : x = (k y (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq220709 eq183921
    | exact resolve eq183921 eq220709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183921
  have eq261599 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq220709 eq222727
    | exact resolve eq222727 eq220709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220709 eq222727
  have eq261705 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35058 eq261599
    | exact resolve eq261599 eq35058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261599
  have eq261706 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq261705
  have eq261709 : x = (k x (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35058 eq261595
    | exact resolve eq261595 eq35058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261595
  have eq261731 : x = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35058 eq261709
    | exact resolve eq261709 eq35058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261709
  have eq261741 : y = (M.op x y) ∨ x = (k x (M.op x y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq261731
       have i₂ := eq140862
       grind)
    | exact superpose eq140862 eq261731
    | exact resolve eq261731 eq140862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261731
  have eq261743 : x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35058 eq261741
    | exact resolve eq261741 eq35058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35058 eq261741
  have eq261744 : (σ x) = (k (σ y) (σ x)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq261743
  have eq261837 : (τ (σ x)) = (k y (τ (σ x))) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq261706 eq108
    | exact resolve eq108 eq261706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261706
  have eq261902 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq30 eq261837
    | exact resolve eq261837 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261837
  have eq261995 : (τ (σ x)) = (k y (τ (σ x))) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq261744 eq108
    | exact resolve eq108 eq261744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261744
  have eq262060 : x = (k y x) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq261995
    | exact resolve eq261995 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261995
  have eq262274 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq261902 eq820
    | (have j0 := eq820 (M.op x y)
       grind)
    | exact resolve eq820 eq261902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261902
  have eq262321 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq262060 eq262274
    | exact resolve eq262274 eq262060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262060 eq262274
  have eq262322 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq262321
  have eq269986 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq254835 eq192607
    | exact resolve eq192607 eq254835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192607
  have eq269988 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq254835 eq223422
    | exact resolve eq223422 eq254835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223422 eq254835
  have eq270092 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq269988
    | exact resolve eq269988 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269988
  have eq270095 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq269986
    | exact resolve eq269986 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269986
  have eq270111 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14492 eq270092
    | exact resolve eq270092 eq14492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270092
  have eq270112 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k x x) := by grind
  clear eq270111
  have eq270113 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14492 eq270095
    | exact resolve eq270095 eq14492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270095
  have eq270124 : y = (M.op x y) ∨ (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq270113
       have i₂ := eq140862
       grind)
    | exact superpose eq140862 eq270113
    | exact resolve eq270113 eq140862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270113
  have eq270126 : y = (M.op x y) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq243811 eq270124
    | exact resolve eq270124 eq243811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243811 eq270124
  have eq270129 : x = (M.op x y) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14492 eq270126
    | exact resolve eq270126 eq14492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14492 eq270126
  have eq270130 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k x x) := by grind
  clear eq270129
  have eq270381 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq270112 eq808
    | (have j0 := eq808 (σ (M.op x y))
       grind)
    | exact resolve eq808 eq270112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270383 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq270112 eq820
    | (have j0 := eq820 (σ (M.op x y))
       grind)
    | exact resolve eq820 eq270112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq270112
  have eq270400 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq270130 eq270383
    | exact resolve eq270383 eq270130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270130 eq270383
  have eq270409 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq270400
       have r₂ := eq270381
       grind)
    | exact resolve eq270400 eq270381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270381 eq270400
  have eq271001 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq270409 eq105117
    | exact resolve eq105117 eq270409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270409
  have eq271103 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (k x x) := by grind
  clear eq271001
  have eq271109 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq226938 eq271103
    | exact resolve eq271103 eq226938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271103
  have eq271111 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq234078 eq271109
    | exact resolve eq271109 eq234078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234078 eq271109
  have eq271112 : y = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq271111
  have eq271135 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq271112
       grind)
    | exact superpose eq271112 eq40
    | exact resolve eq40 eq271112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq271112
  have eq271223 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq271135
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq271135
    | exact resolve eq271135 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271135
  have eq271229 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq271223
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq271223
    | exact resolve eq271223 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271223
  have eq291154 : (τ (σ x)) = (k y (τ (σ x))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq251834 eq108
    | exact resolve eq108 eq251834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq251834
  have eq291223 : x = (k y x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq291154
    | exact resolve eq291154 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291154
  have eq291226 : x = (k y x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq262322 eq291223
    | exact resolve eq291223 eq262322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262322 eq291223
  have eq291229 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k y x) := by
    first
    | (have j1 := eq808 (M.op x y)
       grind)
    | (have r₁ := eq291226
       have r₂ := eq808 (M.op x y)
       grind)
    | exact resolve eq291226 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq291226
  have eq291317 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq291229 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq291229
       grind)
    | exact resolve eq13 eq291229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291229
  have eq291402 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k y x) := by
    intro X0
    first
    | (have j0 := eq291317 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291317
  have eq349678 : ∀ X0 : G, y = (k x (M.op X0 y)) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq178 X0 y (M.op X0 y)
       have i₂ := eq128014 X0
       grind)
    | exact superpose eq128014 eq178
    | (have j1 := eq128014 X0
       grind)
    | exact resolve eq178 eq128014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq128014
  have eq350715 : y = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq349678 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq349678
    | (have j0 := eq349678 x
       grind)
    | exact resolve eq349678 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349678
  have eq350889 : y = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq350715
       have i₂ := eq140862
       grind)
    | exact superpose eq140862 eq350715
    | exact resolve eq350715 eq140862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350715
  have eq350995 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq350889 eq42
    | exact resolve eq42 eq350889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq350889
  have eq351075 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq350995
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq350995
    | exact resolve eq350995 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350995
  have eq351079 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq351075
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq351075
    | exact resolve eq351075 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351075
  have eq351130 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq351079 eq769
    | (have j0 := eq769 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq769 eq351079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq351079
  have eq378502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq351130 eq105117
    | exact resolve eq105117 eq351130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105117 eq351130
  have eq378626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq378502
    | exact resolve eq378502 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378502
  have eq378718 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq378626
       have r₂ := eq27
       grind)
    | exact resolve eq378626 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378626
  have eq378724 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq226938 eq378718
    | exact resolve eq378718 eq226938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226938 eq378718
  have eq379042 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq378724 eq33885
    | (have j0 := eq33885 x y
       grind)
    | exact resolve eq33885 eq378724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33885 eq378724
  have eq379108 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq379042
  have eq379160 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq271229 eq379108
    | exact resolve eq379108 eq271229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271229 eq379108
  have eq379170 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq379160 eq29
    | exact resolve eq29 eq379160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379160
  have eq379536 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq379170
    | exact resolve eq379170 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq379170
  have eq379537 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq379536
  have eq379557 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq379537 eq29
    | exact resolve eq29 eq379537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq379537
  have eq379890 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq379557
    | exact resolve eq379557 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq379557
  have eq379891 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq379890
  have eq379910 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq379891
       grind)
    | exact superpose eq379891 eq18
    | exact resolve eq18 eq379891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380301 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140913
       have i₂ := eq379891
       grind)
    | exact superpose eq379891 eq140913
    | exact resolve eq140913 eq379891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140913
  have eq381055 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq379910 eq197
    | exact resolve eq197 eq379910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq379910
  have eq381235 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq379891 eq381055
    | exact resolve eq381055 eq379891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379891 eq381055
  have eq382099 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq381235 eq380301
    | exact resolve eq380301 eq381235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380301 eq381235
  have eq382299 : x = (M.op x y) := by grind
  clear eq382099
  have eq382308 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq382299
       grind)
    | exact superpose eq382299 eq18
    | exact resolve eq18 eq382299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq382309 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq382299
       grind)
    | exact superpose eq382299 eq22
    | exact resolve eq22 eq382299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq382634 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq140862
       have i₂ := eq382299
       grind)
    | exact superpose eq382299 eq140862
    | exact resolve eq140862 eq382299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140862
  have eq382775 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq382309 eq20
    | exact resolve eq20 eq382309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383759 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq382308 eq207
    | exact resolve eq207 eq382308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq383800 : (M.op x y) = (k y (M.op x y)) ∨ x = (k y x) := by
    first
    | exact superpose eq382308 eq291402
    | exact resolve eq291402 eq382308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291402 eq382308
  have eq383960 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq383800
       have i₂ := eq382299
       grind)
    | exact superpose eq382299 eq383800
    | exact resolve eq383800 eq382299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383800
  have eq383961 : (M.op x y) = (k y (M.op x y)) := by grind
  clear eq383960
  have eq383974 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq383759
       have i₂ := eq382299
       grind)
    | exact superpose eq382299 eq383759
    | exact resolve eq383759 eq382299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382299 eq383759
  have eq384341 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq383961 eq37
    | exact resolve eq37 eq383961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq383961
  have eq384427 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq384341
    | exact resolve eq384341 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq384341
  have eq384429 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq382775 eq384427
    | exact resolve eq384427 eq382775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384427
  have eq384473 : y = (M.op x y) := by
    first
    | exact superpose eq383974 eq382634
    | exact resolve eq382634 eq383974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382634 eq383974
  have eq384680 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq384473
       grind)
    | exact superpose eq384473 eq24
    | exact resolve eq24 eq384473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq384473
  have eq385292 : (σ x) = (σ y) := by
    first
    | exact superpose eq382309 eq384680
    | exact resolve eq384680 eq382309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382309 eq384680
  have eq385416 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq385292 eq26
    | exact resolve eq26 eq385292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq387438 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq384429 eq803
    | exact resolve eq803 eq384429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq384429
  have eq387520 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq385416 eq387438
    | exact resolve eq387438 eq385416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385416 eq387438
  have eq387530 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq385292 eq387520
    | exact resolve eq387520 eq385292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385292 eq387520
  have eq387531 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq387530
  have eq387542 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq387531 eq27
    | exact resolve eq27 eq387531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq387531
  have eq387759 : False := by grind
  exact eq387759

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyy_pxx_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq56 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op (M.op X0 X1) (M.op X0 X1)) X2) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have i₂ := eq14 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq106 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq102
  have eq107 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq106
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq129
  have eq133 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq132
  have eq139 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq16
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : (σ (k (M.op (M.op x y) (M.op x y)) x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq133 eq40
    | exact resolve eq40 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq201 : (σ (k (M.op y y) (M.op x y))) = (k (M.op (σ y) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq42 (M.op y y)
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq42
    | exact resolve eq42 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq107
  have eq219 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq229 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq219 eq14
    | exact resolve eq14 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq277 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq55 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y X0
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq55 X2 X0 x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq55 X0 X0 X0
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X0) X1) ∨ (M.op X0 X0) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 X0
       have i₂ := eq11 X0 (τ X1)
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 X0 (τ X1)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq433 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq45
    | exact resolve eq45 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq451 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq55
    | exact resolve eq55 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1645 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1 X0
       have i₂ := eq56 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq56 eq94
    | (have j0 := eq94 X0 X1 X0
       grind)
    | (have r₁ := eq94 X0 x X0
       have r₂ := eq56 X0 x (M.op X0 x)
       grind)
    | exact resolve eq94 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1661 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1645 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1705 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 (σ X0) X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq280
    | exact resolve eq280 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq10946 : ∀ X0 X1 : G, (M.op (k (τ X0) X1) (k (τ X0) X1)) = (τ (M.op (k X0 (σ X1)) (k X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (k (τ X0) X1) (k (τ X0) X1))
       have i₂ := eq433 X0 X1
       grind)
    | exact superpose eq433 eq16
    | exact resolve eq16 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq11989 : y ≠ y ∨ (M.op x y) = (M.op y y) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq277 eq297
    | (have j0 := eq297 y (M.op x y)
       grind)
    | (have r₁ := eq297 y (M.op x y)
       have r₂ := eq277 y
       grind)
    | exact resolve eq297 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq11994 : (M.op (M.op x y) (M.op x y)) = (k (M.op y y) (M.op x y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq11989
  have eq16270 : (M.op x x) = (k (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1661 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1661
    | (have j0 := eq1661 x y
       grind)
    | exact resolve eq1661 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1661
  have eq21434 : (σ (M.op (M.op x y) (M.op x y))) = (k (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq11994 eq201
    | exact resolve eq201 eq11994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq11994
  have eq21473 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq133 eq21434
    | exact resolve eq21434 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq21434
  have eq21484 : (σ (M.op x x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq16270 eq174
    | exact resolve eq174 eq16270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq16270
  have eq21528 : (M.op (σ x) (σ x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq21484
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq21484
    | exact resolve eq21484 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21484
  have eq456687 : ∀ X0 X1 : G, (M.op (k (τ (σ X0)) X1) (k (τ (σ X0)) X1)) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10946 (σ X0) X1
       have i₂ := eq384 X0 (σ X1)
       grind)
    | exact superpose eq384 eq10946
    | (have j1 := eq384 X0 (σ X1)
       grind)
    | exact resolve eq10946 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq10946
  have eq457155 : ∀ X0 X1 : G, (M.op (k (τ (σ X0)) X1) (k (τ (σ X0)) X1)) = (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq456687 X0 X1
       have i₂ := eq45 (M.op X0 X0)
       grind)
    | exact superpose eq45 eq456687
    | (have j0 := eq456687 X0 X1
       grind)
    | exact resolve eq456687 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq456687
  have eq457316 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (k (τ (σ X0)) X1) (k (τ (σ X0)) X1)) ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq457155 X0 X1
       have i₂ := eq16 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq16 eq457155
    | (have j0 := eq457155 X0 X1
       grind)
    | exact resolve eq457155 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457155
  have eq457342 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq457316 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq457316
    | (have j0 := eq457316 X0 X1
       grind)
    | exact resolve eq457316 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457316
  have eq457352 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = X0 ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq457342 X0 X1
       have i₂ := eq55 X0 X0 X0
       grind)
    | (have i₁ := eq457342 X0 X1
       have i₂ := eq55 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq55 eq457342
    | (have j0 := eq457342 X0 X1
       grind)
    | exact resolve eq457342 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457342
  have eq457358 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op (k X0 X1) (k X0 X1)) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq457352 X0 X1
       have i₂ := eq16 X1
       grind)
    | exact superpose eq16 eq457352
    | (have j0 := eq457352 X0 X1
       grind)
    | exact resolve eq457352 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457352
  have eq457361 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq457358 X0 X1
       have i₂ := eq16 X1
       grind)
    | exact superpose eq16 eq457358
    | (have j0 := eq457358 X0 X1
       grind)
    | exact resolve eq457358 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457358
  have eq957731 : (M.op (σ y) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21473 eq457361
    | (have j0 := eq457361 (M.op (σ y) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq457361 eq21473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21473
  have eq957733 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21528 eq457361
    | (have j0 := eq457361 (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)
       grind)
    | exact resolve eq457361 eq21528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21528 eq457361
  have eq958898 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq957733
       have i₂ := eq55 sF2 sF2 sF2
       grind)
    | (have i₁ := eq957733
       have i₂ := eq55 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq55 eq957733
    | exact resolve eq957733 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957733
  have eq958899 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq958898
  have eq958901 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq957731
       have i₂ := eq55 sF1 sF1 sF1
       grind)
    | (have i₁ := eq957731
       have i₂ := eq55 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq55 eq957731
    | exact resolve eq957731 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957731
  have eq958902 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq958901
  have eq959120 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq958899
       have i₂ := eq55 sF1 sF1 sF1
       grind)
    | (have i₁ := eq958899
       have i₂ := eq55 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq55 eq958899
    | exact resolve eq958899 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958899
  have eq959121 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq958902
       have i₂ := eq55 sF3 sF3 sF3
       grind)
    | (have i₁ := eq958902
       have i₂ := eq55 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq55 eq958902
    | exact resolve eq958902 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958902
  have eq959150 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq959120 eq55
    | exact resolve eq55 eq959120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq959152 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq959120 eq56
    | exact resolve eq56 eq959120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq959120
  have eq965058 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq959121 eq959152
    | exact resolve eq959152 eq959121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959152
  have eq965133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27 eq965058
    | exact resolve eq965058 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965058
  have eq965134 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq965133
       have r₂ := eq28
       grind)
    | exact resolve eq965133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965133
  have eq965137 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq965134 eq170
    | exact resolve eq170 eq965134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965134
  have eq965509 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq29 eq965137
    | exact resolve eq965137 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965137
  have eq965510 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq965509
  have eq968320 : (τ (σ (M.op x y))) = (M.op y y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq965510 eq139
    | exact resolve eq139 eq965510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965510
  have eq968710 : (M.op x y) = (M.op y y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq31 eq968320
    | exact resolve eq968320 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968320
  have eq968711 : (M.op x y) = (M.op y y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq968710
  have eq968881 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1705 y x
       have i₂ := eq968711
       grind)
    | exact superpose eq968711 eq1705
    | exact resolve eq1705 eq968711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705 eq968711
  have eq969031 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq968881 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq968881
    | (have j0 := eq968881 X0
       grind)
    | exact resolve eq968881 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968881
  have eq969143 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq969031
    | (have j0 := eq969031 X0
       grind)
    | exact resolve eq969031 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969031
  have eq1009669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq959150 eq969143
    | exact resolve eq969143 eq959150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959150 eq969143
  have eq1009778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1009669
  have eq1009785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq1009778
    | exact resolve eq1009778 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009778
  have eq1009788 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq1009785
       have r₂ := eq28
       grind)
    | exact resolve eq1009785 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009785
  have eq1009794 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1009788 eq170
    | exact resolve eq170 eq1009788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq1009788
  have eq1010173 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq1009794
    | exact resolve eq1009794 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1009794
  have eq1010174 : x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq1010173
  have eq1010346 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1010174 eq229
    | exact resolve eq229 eq1010174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq1010361 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq1010174 eq451
    | exact resolve eq451 eq1010174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq1010535 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq21 eq1010361
    | (have j0 := eq1010361 X0
       grind)
    | exact resolve eq1010361 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010361
  have eq1010648 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq1010535 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1010535
    | (have j0 := eq1010535 X0
       grind)
    | exact resolve eq1010535 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010535
  have eq1010700 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq52
       have i₂ := eq1010346
       grind)
    | exact superpose eq1010346 eq52
    | exact resolve eq52 eq1010346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1010346
  have eq1011056 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq1010700
    | exact resolve eq1010700 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1010700
  have eq1012829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq959121 eq1010648
    | exact resolve eq1010648 eq959121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959121 eq1010648
  have eq1012934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27 eq1012829
    | exact resolve eq1012829 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012829
  have eq1012937 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1012934
       have r₂ := eq28
       grind)
    | exact resolve eq1012934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012934
  have eq1117658 : (τ (σ (M.op x y))) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1012937 eq139
    | exact resolve eq139 eq1012937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq1012937
  have eq1118075 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq31 eq1117658
    | exact resolve eq1117658 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1117658
  have eq1118076 : (M.op x y) = (M.op y y) := by grind
  clear eq1118075
  have eq1118258 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq277 y
       have i₂ := eq1118076
       grind)
    | exact superpose eq1118076 eq277
    | exact resolve eq277 eq1118076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq1118076
  have eq1118460 : x = y := by
    first
    | exact superpose eq1010174 eq1118258
    | exact resolve eq1118258 eq1010174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010174 eq1118258
  have eq1118663 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1118460
       grind)
    | exact superpose eq1118460 eq25
    | exact resolve eq25 eq1118460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1118460
  have eq1119902 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1118663
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1118663
    | exact resolve eq1118663 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1118663
  have eq1120695 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1119902 eq27
    | exact resolve eq27 eq1119902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1119902
  have eq1121970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1011056 eq1120695
    | exact resolve eq1120695 eq1011056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011056 eq1120695
  have eq1122274 : False := by grind
  exact eq1122274

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq25 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 X2) (M.op X1 X2)) X1
       have i₂ := eq9 (M.op X1 X2) X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) (M.op X0 X1)) X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq168 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq159 y x
       grind)
    | exact superpose eq159 eq16
    | (have j1 := eq159 y x
       grind)
    | exact resolve eq16 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq159 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq210 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1 X0
       have i₂ := eq25 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq25 eq34
    | (have j0 := eq34 X0 X1 X0
       grind)
    | (have r₁ := eq34 X0 x X0
       have r₂ := eq25 X0 x (M.op X0 x)
       grind)
    | exact resolve eq34 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq34
  have eq216 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq867 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq168
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq168
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq168
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq168
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq168 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq867
  have eq1789 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) ∨ (τ (M.op (σ X0) X1)) = (k (τ (M.op (M.op (σ X0) X1) (M.op (σ X0) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) X0
       have i₂ := eq216 (σ X0) X1
       grind)
    | exact superpose eq216 eq31
    | (have j1 := eq216 (σ X0) X1
       grind)
    | exact resolve eq31 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1898 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 (τ X1) (τ X0)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq177
    | (have j0 := eq177 (τ X1) (τ X0)
       grind)
    | exact resolve eq177 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq177
  have eq1930 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1898 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1898
    | (have j0 := eq1898 X0 X1
       grind)
    | exact resolve eq1898 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq1947 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1930 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq1930
    | (have j0 := eq1930 X0 X1
       grind)
    | exact resolve eq1930 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq1960 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1947 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1947
    | (have j0 := eq1947 X0 X1
       grind)
    | exact resolve eq1947 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq1967 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1960 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1960
    | (have j0 := eq1960 X0 X1
       grind)
    | exact resolve eq1960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq1973 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1967 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq1967
    | (have j0 := eq1967 X0 X1
       grind)
    | exact resolve eq1967 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1967
  have eq1978 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1973 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1973
    | (have j0 := eq1973 X0 X1
       grind)
    | exact resolve eq1973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq1983 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1978 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1978
    | (have j0 := eq1978 X0 X1
       grind)
    | exact resolve eq1978 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1978
  have eq8652 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq868
       grind)
    | exact superpose eq868 eq16
    | exact resolve eq16 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq8653 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8652
       have r₂ := eq22 x
       grind)
    | exact resolve eq8652 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8652
  have eq24526 : (σ x) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (τ (σ (M.op y y))) = (k (τ (M.op (σ (M.op y y)) (σ (M.op y y)))) x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1789 x (σ y)
       have i₂ := eq8653
       grind)
    | exact superpose eq8653 eq1789
    | exact resolve eq1789 eq8653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq8653
  have eq24572 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) ∨ (τ (σ (M.op y y))) = (k (τ (M.op (σ (M.op y y)) (σ (M.op y y)))) x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24526
       have i₂ := eq22 (M.op y y)
       grind)
    | exact superpose eq22 eq24526
    | exact resolve eq24526 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24526
  have eq24578 : (σ x) = (σ y) ∨ (τ (σ (M.op y y))) = (k (τ (M.op (σ (M.op y y)) (σ (M.op y y)))) x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24572
       have i₂ := eq24 y y y
       grind)
    | (have i₁ := eq24572
       have i₂ := eq24 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq24 eq24572
    | exact resolve eq24572 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24572
  have eq24579 : (σ x) = (σ y) ∨ (τ (σ (M.op y y))) = (k (τ (M.op (σ (M.op y y)) (σ (M.op y y)))) x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq24578
  have eq24582 : (τ (σ (M.op y y))) = (k (τ (σ (M.op (M.op y y) (M.op y y)))) x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24579
       have i₂ := eq22 (M.op y y)
       grind)
    | exact superpose eq22 eq24579
    | exact resolve eq24579 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24579
  have eq24585 : (τ (σ (M.op y y))) = (k (M.op (M.op y y) (M.op y y)) x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24582
       have i₂ := eq10 (M.op (M.op y y) (M.op y y))
       grind)
    | exact superpose eq10 eq24582
    | exact resolve eq24582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24582
  have eq24589 : (k y x) = (τ (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24585
       have i₂ := eq24 y y y
       grind)
    | (have i₁ := eq24585
       have i₂ := eq24 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq24 eq24585
    | exact resolve eq24585 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24585
  have eq24591 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24589
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq24589
    | exact resolve eq24589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24589
  have eq24602 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1983 y x
       have i₂ := eq24591
       grind)
    | exact superpose eq24591 eq1983
    | (have j0 := eq1983 y x
       grind)
    | (have r₁ := eq1983 y x
       have r₂ := eq24591
       grind)
    | exact resolve eq1983 eq24591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983 eq24591
  have eq24613 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq24602
  have eq24614 : x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq24613
  have eq24626 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24614
       grind)
    | exact superpose eq24614 eq16
    | exact resolve eq16 eq24614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24614
  have eq24627 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq24626
       have r₂ := eq22 x
       grind)
    | exact resolve eq24626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24626
  have eq24629 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24627
       grind)
    | exact superpose eq24627 eq10
    | exact resolve eq10 eq24627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24627
  have eq24745 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24629
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24629
    | exact resolve eq24629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24629
  have eq24747 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24745
       grind)
    | exact superpose eq24745 eq16
    | exact resolve eq16 eq24745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24745
  have eq24748 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq24747
       have r₂ := eq22 x
       grind)
    | exact resolve eq24747 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24747
  have eq24807 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq24 X0 y y
       have i₂ := eq24748
       grind)
    | exact superpose eq24748 eq24
    | exact resolve eq24 eq24748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq24841 : x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq216 x y
       have i₂ := eq24807 x
       grind)
    | exact superpose eq24807 eq216
    | exact resolve eq216 eq24807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq24807
  have eq24946 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24841
       grind)
    | exact superpose eq24841 eq16
    | exact resolve eq16 eq24841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24841
  have eq24948 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq24946
       have r₂ := eq22 x
       grind)
    | exact resolve eq24946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24946
  have eq24955 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq168
       have i₂ := eq24948
       grind)
    | exact superpose eq24948 eq168
    | exact resolve eq168 eq24948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq24948
  have eq24973 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24955
  have eq24983 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24973
       have i₂ := eq24748
       grind)
    | exact superpose eq24748 eq24973
    | exact resolve eq24973 eq24748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24748 eq24973
  have eq24989 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq24983
       have r₂ := eq16
       grind)
    | exact resolve eq24983 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24983
  have eq24995 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24989
       grind)
    | exact superpose eq24989 eq10
    | exact resolve eq10 eq24989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24989
  have eq25146 : x = y := by
    first
    | (have i₁ := eq24995
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24995
    | exact resolve eq24995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24995
  have eq25449 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25146
       grind)
    | exact superpose eq25146 eq16
    | exact resolve eq16 eq25146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25146
  have eq25452 : False := by grind
  exact eq25452

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X1) (M.op X0 X0)) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X1) = X1 ∨ (M.op X1 X1) = (k X1 X2) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X1) = X1 ∨ (M.op X1 X1) = (k X1 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq40 X0 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X1) (M.op X0 X0)) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq38 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 (M.op X0 X0) X2
       have r₂ := eq12 (M.op X0 X0) (M.op (M.op (M.op X0 X0) X2) (M.op X0 X0))
       grind)
    | (have r₁ := eq38 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq101 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq897 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq898 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq897 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq897 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq897 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq1564 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq101 X1 X0
       grind)
    | exact superpose eq101 eq9
    | exact resolve eq9 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1893 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq898 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq3190 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X2 X2) (M.op X2 X2))) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq1564 (M.op (M.op X0 x) X0) (M.op X2 X2)
       have i₂ := eq47 X2 X0 x
       grind)
    | exact superpose eq47 eq1564
    | (have j1 := eq47 X2 X0 X2
       grind)
    | exact resolve eq1564 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq3339 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq3190 X0 X2
       have i₂ := eq1564 X2 X2
       grind)
    | exact superpose eq1564 eq3190
    | (have j0 := eq3190 X0 X2
       grind)
    | exact resolve eq3190 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564 eq3190
  have eq3345 : ∀ X0 X2 : G, (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have j0 := eq3339 X0 X2
       have j1 := eq1893 X2 X0
       grind)
    | (have r₁ := eq3339 x X0
       have r₂ := eq1893 X0 x
       grind)
    | (have r₁ := eq3339 x x
       have r₂ := eq1893 x x
       grind)
    | exact resolve eq3339 eq1893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893 eq3339
  have eq6295 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3345 (σ X0) (σ X1)
       grind)
    | exact superpose eq3345 eq15
    | exact resolve eq15 eq3345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6310 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6295 X0 X1
       have i₂ := eq3345 X0 X1
       grind)
    | exact superpose eq3345 eq6295
    | exact resolve eq6295 eq3345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345 eq6295
  have eq6324 : False := by grind
  exact eq6324

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq35 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq54 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq43 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq43 X0 X1
       grind)
    | exact resolve eq51 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq51
  have eq111 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X2 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq20 X1 X0 x
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq169 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1173 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (M.op X0 x) X0 X1
       have i₂ := eq46 X0 X1 x
       grind)
    | exact superpose eq46 eq111
    | (have j1 := eq46 X0 X1 x
       grind)
    | exact resolve eq111 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq111
  have eq1226 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1173 X0 X1
       have j1 := eq169 X1 X0
       grind)
    | (have r₁ := eq1173 X0 X1
       have r₂ := eq169 X0 X1
       grind)
    | (have r₁ := eq1173 X1 X0
       have r₂ := eq169 X0 X1
       grind)
    | exact resolve eq1173 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq1173
  have eq34005 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1226 (σ X0) (σ X1)
       grind)
    | exact superpose eq1226 eq15
    | exact resolve eq15 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34024 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34005 X0 X1
       have i₂ := eq1226 X0 X1
       grind)
    | exact superpose eq1226 eq34005
    | exact resolve eq34005 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq34005
  have eq34046 : False := by grind
  exact eq34046

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  clear eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq56 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq78 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq79 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq83 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq79 sF2
       grind)
    | exact superpose eq79 eq50
    | exact resolve eq50 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq84 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq83
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq83
    | exact resolve eq83 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq83
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq106
    | exact resolve eq106 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq234 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq585 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq1865 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq584 eq573
    | exact resolve eq573 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq1869 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq585 eq573
    | exact resolve eq573 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq585
  have eq2085 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq582 X1 X0
       grind)
    | exact superpose eq582 eq14
    | exact resolve eq14 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq2203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2203
    | exact resolve eq2203 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203
  have eq2207 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2204
       have r₂ := eq28
       grind)
    | exact resolve eq2204 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204
  have eq2209 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2207
    | exact resolve eq2207 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq2255 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2209 eq28
    | exact resolve eq28 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2258 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2209 eq68
    | (have r₁ := eq68
       have r₂ := eq2209
       grind)
    | exact resolve eq68 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq2275 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2209 eq1869
    | exact resolve eq1869 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq2277 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2258
  have eq2278 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2275
    | exact resolve eq2275 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2280 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2209 eq2278
    | exact resolve eq2278 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209 eq2278
  have eq2305 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2280
  have eq2365 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2305 eq2085
    | exact resolve eq2085 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305
  have eq2926 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2277 eq108
    | exact resolve eq108 eq2277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq2277
  have eq2930 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2926
  have eq3025 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2930 eq2365
    | exact resolve eq2365 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365 eq2930
  have eq3054 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3025
  have eq3059 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq3054
       have r₂ := eq2255
       grind)
    | exact resolve eq3054 eq2255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2255 eq3054
  have eq3126 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3059 eq30
    | exact resolve eq30 eq3059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3059
  have eq3161 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq3126
    | exact resolve eq3126 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3126
  have eq3162 : x = (M.op x y) ∨ x = y := by grind
  clear eq3161
  have eq3165 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3162 eq21
    | exact resolve eq21 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3167 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq3162 eq51
    | exact resolve eq51 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3195 : y = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3162 eq1865
    | exact resolve eq1865 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq3198 : y = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq3195
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3195
    | exact resolve eq3195 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195
  have eq3208 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq3165
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3165
    | exact resolve eq3165 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165
  have eq3221 : (k y x) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq3208 eq92
    | exact resolve eq92 eq3208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq3257 : (k y x) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq114 eq3221
    | exact resolve eq3221 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq3221
  have eq3316 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3162 eq3198
    | exact resolve eq3198 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3198
  have eq3346 : y = (M.op x x) ∨ x = y := by grind
  clear eq3316
  have eq15338 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = y := by
    first
    | exact superpose eq234 eq3167
    | exact resolve eq3167 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq3167
  have eq15417 : x = (M.op (M.op x y) (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq15338
       have i₂ := eq2085 x x
       grind)
    | exact superpose eq2085 eq15338
    | exact resolve eq15338 eq2085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15338
  have eq16744 : x ≠ (M.op x y) ∨ (k (M.op x x) (M.op x y)) = (M.op (M.op x x) (M.op x x)) ∨ x = y := by
    first
    | exact superpose eq15417 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq15417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15417
  have eq16794 : (k (M.op x x) (M.op x y)) = (M.op (M.op x x) (M.op x x)) ∨ x = y := by
    first
    | (have r₁ := eq16744
       have r₂ := eq3162
       grind)
    | exact resolve eq16744 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162 eq16744
  have eq16795 : x = (k (M.op x x) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq16794
       have i₂ := eq2085 x x
       grind)
    | exact superpose eq2085 eq16794
    | exact resolve eq16794 eq2085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085 eq16794
  have eq17914 : x = (k y (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq16795
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq16795
    | exact resolve eq16795 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346 eq16795
  have eq17921 : x = (k y (M.op x y)) ∨ x = y := by grind
  clear eq17914
  have eq17927 : x = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq17921 eq3257
    | exact resolve eq3257 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3257 eq17921
  have eq17930 : x = (k y x) ∨ x = y := by grind
  clear eq17927
  have eq17941 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq17930
       grind)
    | exact superpose eq17930 eq76
    | exact resolve eq76 eq17930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq17930
  have eq17950 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq17941
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17941
    | exact resolve eq17941 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17941
  have eq18081 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq17950 eq11
    | (have j0 := eq11 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq17950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17950
  have eq18082 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18081
  have eq18096 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq18082
    | exact resolve eq18082 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18082
  have eq18219 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18096 eq28
    | exact resolve eq28 eq18096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18096
  have eq18289 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18219
       have r₂ := eq3208
       grind)
    | exact resolve eq18219 eq3208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3208 eq18219
  have eq18318 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq18289 eq30
    | exact resolve eq30 eq18289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18289
  have eq18446 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq18318
    | exact resolve eq18318 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18318
  have eq18447 : x = y := by grind
  clear eq18446
  have eq18450 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18447
       grind)
    | exact superpose eq18447 eq19
    | exact resolve eq19 eq18447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq18451 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq18447
       grind)
    | exact superpose eq18447 eq25
    | exact resolve eq25 eq18447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18447
  have eq18498 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18451
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18451
    | exact resolve eq18451 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq18451
  have eq18501 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18498 eq27
    | exact resolve eq27 eq18498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18498
  have eq18813 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18501 eq84
    | exact resolve eq84 eq18501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq18501
  have eq18903 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18813
       have i₂ := eq18450
       grind)
    | exact superpose eq18450 eq18813
    | exact resolve eq18813 eq18450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18450 eq18813
  have eq18907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18903 eq15
    | exact resolve eq15 eq18903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18903
  have eq18950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18907
    | exact resolve eq18907 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18907
  have eq18959 : False := by grind
  exact eq18959
