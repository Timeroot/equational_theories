import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyx_x_pxy_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X0 X4) X5) X6) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq16 X0 X4 X5 X6
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq16 X0 X0 X2 X3
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq16 X0 X1 X2 (M.op (M.op X0 X1) X2)
       have i₂ := eq16 (M.op (M.op X0 X1) X2) X3 X4 X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq36
    | exact resolve eq36 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq191 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq192 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq191
    | exact resolve eq191 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq193 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq190
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq190
    | exact resolve eq190 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq202 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq241 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq230
    | exact resolve eq230 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq248 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq259 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq248
    | exact resolve eq248 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq377 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq788 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq789 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) = X1 ∨ (M.op (σ x) (σ x)) = (k (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq180 eq12
    | (have j0 := eq12 (M.op (M.op (σ x) (σ y)) X0) X1
       grind)
    | exact resolve eq12 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 ∨ (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq12
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq821 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq834 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op (σ x) (σ x)) = X1 ∨ (M.op (σ x) (σ x)) = (k (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq180 eq818
    | (have j0 := eq818 X0 X1
       grind)
    | (have r₁ := eq818 X0 (M.op (M.op (σ x) (σ y)) X0)
       have r₂ := eq180 X0 (M.op (M.op (σ x) (σ y)) X0)
       grind)
    | exact resolve eq818 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq818
  have eq880 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq828 X0
       grind)
    | exact superpose eq828 eq16
    | (have j1 := eq828 X0
       grind)
    | exact resolve eq16 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X0 X2 x
       have i₂ := eq828 X0
       grind)
    | exact superpose eq828 eq16
    | (have j1 := eq828 X0
       grind)
    | exact resolve eq16 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 x X2
       have i₂ := eq181 X0 x X1
       grind)
    | (have i₁ := eq181 X0 X0 x
       have i₂ := eq181 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X0 X2) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) x
       have i₂ := eq181 X0 X1 x
       grind)
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq181 X0 X1 x
       grind)
    | exact superpose eq181 eq12
    | (have r₁ := eq12 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq181 X1 X1 (M.op X1 X1)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq181 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1086 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X2) (M.op X0 X2)) ∨ (M.op X0 X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1083 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1650 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (k X0 X0) X4) X5) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq175 X0 X1 X2 X3 X0 X4 X5
       have i₂ := eq828 X0
       grind)
    | exact superpose eq828 eq175
    | (have j1 := eq828 X0
       grind)
    | exact resolve eq175 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq3223 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq788
       grind)
    | exact superpose eq788 eq39
    | exact resolve eq39 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3224 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3223
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3223
    | exact resolve eq3223 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3223
  have eq3226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3224
    | exact resolve eq3224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3224
  have eq10935 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq830 X0 X1 X2 X3
       grind)
    | exact superpose eq830 eq16
    | (have j1 := eq830 X0 X1 X2 X3
       grind)
    | exact resolve eq16 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10939 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (k X0 X0) X4) X5) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq183 X0 X1 X2 X3 X4 X5
       have i₂ := eq830 X0 X1 X2 X3
       grind)
    | exact superpose eq830 eq183
    | (have j1 := eq830 X0 X1 X2 X3
       grind)
    | exact resolve eq183 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq10979 : ∀ X0 X1 X2 X3 : G, (k X0 X0) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq830 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq20487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3226 eq789
    | exact resolve eq789 eq3226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20496 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq20487
       have r₂ := eq27
       grind)
    | exact resolve eq20487 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20487
  have eq20504 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20496 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20496
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq20496
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20496
       grind)
    | exact resolve eq12 eq20496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20496
  have eq20525 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq20504
  have eq20537 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq20525
       have r₂ := eq26
       grind)
    | exact resolve eq20525 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20525
  have eq20545 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3226 eq20537
    | exact resolve eq20537 eq3226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3226 eq20537
  have eq20546 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq20545
       have r₂ := eq27
       grind)
    | exact resolve eq20545 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20545
  have eq20548 : y = (k y (τ (σ x))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20546 eq259
    | exact resolve eq259 eq20546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20546
  have eq20587 : y = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq20548
    | exact resolve eq20548 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20548
  have eq20593 : (M.op x y) = (M.op y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq20587
       have r₂ := eq13 y x
       grind)
    | exact resolve eq20587 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20587
  have eq20597 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq20593
       grind)
    | exact superpose eq20593 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20593
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20593
       grind)
    | exact resolve eq12 eq20593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20593
  have eq20628 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq20597
       have r₂ := eq13 y x
       grind)
    | exact resolve eq20597 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20597
  have eq20636 : (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq20628
       have r₂ := eq18
       grind)
    | exact resolve eq20628 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20628
  have eq20640 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq20636
       grind)
    | exact superpose eq20636 eq39
    | exact resolve eq39 eq20636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20636
  have eq20644 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq20640
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20640
    | exact resolve eq20640 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20640
  have eq20648 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq20 eq20644
    | exact resolve eq20644 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20644
  have eq20653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq20648 eq789
    | exact resolve eq789 eq20648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20662 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq20653
       have r₂ := eq27
       grind)
    | exact resolve eq20653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20653
  have eq22111 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq20662 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20662
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq20662
       grind)
    | exact resolve eq12 eq20662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20662
  have eq22134 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq22111
  have eq22147 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq22134
       have r₂ := eq26
       grind)
    | exact resolve eq22134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22134
  have eq22156 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq20648 eq22147
    | exact resolve eq22147 eq20648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20648 eq22147
  have eq22157 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq22156
       have r₂ := eq27
       grind)
    | exact resolve eq22156 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22156
  have eq22159 : y = (k y (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq22157 eq259
    | exact resolve eq259 eq22157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq22157
  have eq22200 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq29 eq22159
    | exact resolve eq22159 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22159
  have eq22201 : y = (k y x) := by grind
  clear eq22200
  have eq22213 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq788
       have i₂ := eq22201
       grind)
    | exact superpose eq22201 eq788
    | exact resolve eq788 eq22201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq22215 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq22201
       grind)
    | exact superpose eq22201 eq39
    | exact resolve eq39 eq22201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22218 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq22215
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22215
    | exact resolve eq22215 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22215
  have eq22231 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq22218 eq789
    | exact resolve eq789 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq24263 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq22213
       grind)
    | exact superpose eq22213 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq22213
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq22213
       grind)
    | exact resolve eq12 eq22213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22213
  have eq24287 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq24263
  have eq24300 : x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq24287
       have r₂ := eq18
       grind)
    | exact resolve eq24287 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24287
  have eq24309 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24300
       have i₂ := eq22201
       grind)
    | exact superpose eq22201 eq24300
    | exact resolve eq24300 eq22201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22201 eq24300
  have eq24310 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq24309
  have eq24313 : x = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq24310
       have i₂ := eq828 y
       grind)
    | exact superpose eq828 eq24310
    | (have j1 := eq828 y
       grind)
    | exact resolve eq24310 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24325 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1044 y X1 x
       have i₂ := eq24310
       grind)
    | exact superpose eq24310 eq1044
    | exact resolve eq1044 eq24310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24329 : x ≠ x ∨ x = y ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq24310
       grind)
    | exact superpose eq24310 eq12
    | exact resolve eq12 eq24310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24330 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y y x x
       have i₂ := eq24310
       grind)
    | exact superpose eq24310 eq16
    | exact resolve eq16 eq24310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24333 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x X0) X1) = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ y = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 y y X2 X3 x x
       have i₂ := eq24310
       grind)
    | exact superpose eq24310 eq177
    | exact resolve eq177 eq24310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24334 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 y y x
       have i₂ := eq24310
       grind)
    | exact superpose eq24310 eq181
    | exact resolve eq181 eq24310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq24310
  have eq24350 : x = (k y y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq24329
  have eq24354 : ∀ X0 X1 X3 : G, (M.op (M.op x X0) X1) = (M.op (M.op x x) X3) ∨ y = (M.op x y) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq24333 X0 X1 x X3
       have i₂ := eq16 x X0 X1 x
       grind)
    | exact superpose eq16 eq24333
    | exact resolve eq24333 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24333
  have eq24360 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24350 eq24313
    | exact resolve eq24313 eq24350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24313
  have eq24361 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq24354 X0 X1 x
       have i₂ := eq202 x
       grind)
    | exact superpose eq202 eq24354
    | exact resolve eq24354 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq24354
  have eq24365 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24330 eq24361
    | (have j1 := eq24330 y (M.op x y)
       grind)
    | exact resolve eq24361 eq24330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24361
  have eq24368 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq24365
       have i₂ := eq828 sF0
       grind)
    | exact superpose eq828 eq24365
    | (have j1 := eq828 (M.op x y)
       grind)
    | exact resolve eq24365 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24391 : x ≠ x ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24365 eq12
    | exact resolve eq12 eq24365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24365
  have eq24412 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq24391
  have eq24894 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq24325 X0 x
       have i₂ := eq828 x
       grind)
    | exact superpose eq828 eq24325
    | (have j1 := eq828 x
       grind)
    | exact resolve eq24325 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24956 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq24325 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq24325 X0 y
       grind)
    | exact superpose eq24325 eq18
    | (have j1 := eq24325 y X0
       grind)
    | exact resolve eq18 eq24325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24325
  have eq25035 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24956 eq24894
    | (have j0 := eq24894 y
       grind)
    | exact resolve eq24894 eq24956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24894
  have eq25043 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24956 eq25035
    | exact resolve eq25035 eq24956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25035
  have eq25078 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq24956 x
       grind)
    | exact superpose eq24956 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq24956 x
       grind)
    | exact resolve eq13 eq24956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25544 : ∀ X0 X1 X2 : G, (k x x) = (M.op (M.op (M.op x X0) X1) X2) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq880 x x X2 x
       have i₂ := eq24334 X0
       grind)
    | (have i₁ := eq880 x X0 X2 x
       have i₂ := eq24334 X0
       grind)
    | exact superpose eq24334 eq880
    | (have j0 := eq880 x X0 X1 X2
       grind)
    | exact resolve eq880 eq24334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq24334
  have eq25609 : ∀ X0 : G, (k x x) = (M.op x x) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25544 X0 x x
       have i₂ := eq16 x X0 x x
       grind)
    | exact superpose eq16 eq25544
    | (have j0 := eq25544 X0 x x
       grind)
    | exact resolve eq25544 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25544
  have eq25630 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24956 eq25609
    | (have j0 := eq25609 X0
       grind)
    | exact resolve eq25609 eq24956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25609
  have eq25641 : ∀ X0 : G, (M.op x y) = (k x x) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25043 eq25630
    | exact resolve eq25630 eq25043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25630
  have eq25897 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq24350
       grind)
    | exact superpose eq24350 eq40
    | exact resolve eq40 eq24350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24350
  have eq25902 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25897
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25897
    | exact resolve eq25897 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25897
  have eq25906 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25902
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25902
    | exact resolve eq25902 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25902
  have eq25988 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq25043
       grind)
    | exact superpose eq25043 eq39
    | exact resolve eq39 eq25043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25993 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25988
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25988
    | exact resolve eq25988 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25988
  have eq25997 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq25993
    | exact resolve eq25993 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25993
  have eq26206 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq22231 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq22231
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq22231
       grind)
    | exact resolve eq12 eq22231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22231
  have eq26231 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26206
  have eq26245 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26231
       have r₂ := eq26
       grind)
    | exact resolve eq26231 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26231
  have eq26254 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22218 eq26245
    | exact resolve eq26245 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26245
  have eq26255 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26254
  have eq26258 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26255 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq26255
       grind)
    | exact resolve eq13 eq26255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26265 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26255 eq1044
    | exact resolve eq1044 eq26255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26269 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26255 eq12
    | exact resolve eq12 eq26255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26270 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26255 eq16
    | exact resolve eq16 eq26255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26255
  have eq26291 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26269
  have eq26388 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq26265 X0 sF2
       have i₂ := eq828 sF2
       grind)
    | exact superpose eq828 eq26265
    | (have j1 := eq828 (σ x)
       grind)
    | exact resolve eq26265 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26441 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26265 eq26
    | (have j1 := eq26265 (σ y) X0
       grind)
    | exact resolve eq26 eq26265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26446 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26265 eq241
    | exact resolve eq241 eq26265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq26455 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ X1 ∨ (σ x) = (k (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26265 eq13
    | (have j0 := eq13 (σ x) X1
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) X1)
       have r₂ := eq26265 (σ x) X1
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) X0)
       have r₂ := eq26265 X0 (σ x)
       grind)
    | exact resolve eq13 eq26265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26461 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26265 eq828
    | exact resolve eq828 eq26265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26265
  have eq26511 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26441 eq26388
    | (have j0 := eq26388 (σ y)
       grind)
    | exact resolve eq26388 eq26441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26388
  have eq26537 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq25906 eq883
    | (have j0 := eq883 (σ y) X1 x
       grind)
    | exact resolve eq883 eq25906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26900 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26441 eq828
    | exact resolve eq828 eq26441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26981 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq26441 eq26270
    | (have j0 := eq26270 (σ y) X1
       grind)
    | exact resolve eq26270 eq26441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26270 eq26441
  have eq27084 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have j0 := eq26981 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26981
  have eq27674 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26291 eq115
    | exact resolve eq115 eq26291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq27689 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq27674
    | exact resolve eq27674 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27674
  have eq27747 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq883 y X1 x
       have i₂ := eq27689
       grind)
    | exact superpose eq27689 eq883
    | (have j0 := eq883 y X1 x
       grind)
    | exact resolve eq883 eq27689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27751 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq24330 eq27747
    | (have j0 := eq27747 X0 X1
       have j1 := eq24330 X0 X1
       grind)
    | exact resolve eq27747 eq24330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24330 eq27747
  have eq28150 : ∀ X0 X1 X4 : G, (M.op X0 X4) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq10935 X0 X1 x x
       grind)
    | exact superpose eq10935 eq16
    | (have j1 := eq10935 X0 X1 x x
       grind)
    | exact resolve eq16 eq10935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28169 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) X5) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq177 X0 x x x X4 X5
       have i₂ := eq10935 X0 x x x
       grind)
    | exact superpose eq10935 eq177
    | (have j1 := eq10935 X0 x x x
       grind)
    | exact resolve eq177 eq10935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq10935
  have eq28288 : ∀ X0 X4 : G, (M.op X0 X4) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X4
    first
    | exact superpose eq28169 eq28150
    | (have j0 := eq28150 X0 x X4
       have j1 := eq28169 X0 X4 x
       grind)
    | exact resolve eq28150 eq28169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28150 eq28169
  have eq29346 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq24360
       grind)
    | exact superpose eq24360 eq40
    | exact resolve eq40 eq24360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq24360
  have eq29354 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29346
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29346
    | exact resolve eq29346 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29346
  have eq29359 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29354
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29354
    | exact resolve eq29354 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29354
  have eq29363 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24956 eq29359
    | exact resolve eq29359 eq24956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24956 eq29359
  have eq29373 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29363 eq883
    | (have j0 := eq883 (σ y) X1 x
       grind)
    | exact resolve eq883 eq29363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq29611 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq24368 eq174
    | exact resolve eq174 eq24368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24368
  have eq29794 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq39 x
       have i₂ := eq25641 X0
       grind)
    | exact superpose eq25641 eq39
    | (have j1 := eq25641 X0
       grind)
    | exact resolve eq39 eq25641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25641
  have eq29803 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29794 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29794
    | (have j0 := eq29794 X0
       grind)
    | exact resolve eq29794 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29794
  have eq29808 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq29803
    | (have j0 := eq29803 X0
       grind)
    | exact resolve eq29803 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29803
  have eq29918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26511 eq25997
    | exact resolve eq25997 eq26511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29935 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq29918
       have r₂ := eq27
       grind)
    | exact resolve eq29918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29918
  have eq30080 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq29611
  have eq30085 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq30080
       have r₂ := eq24412
       grind)
    | exact resolve eq30080 eq24412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24412 eq30080
  have eq30146 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30085 eq41
    | exact resolve eq41 eq30085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq30154 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq30146
    | exact resolve eq30146 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30146
  have eq30158 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30154
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30154
    | exact resolve eq30154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30154
  have eq35183 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29935 eq26446
    | exact resolve eq26446 eq29935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29935
  have eq35218 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq35183
  have eq35250 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq35218
    | exact resolve eq35218 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35218
  have eq35267 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq25078 x
       grind)
    | (have r₁ := eq35250
       have r₂ := eq25078 x
       grind)
    | (have r₁ := eq35250
       have r₂ := eq25078 y
       grind)
    | exact resolve eq35250 eq25078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25078 eq35250
  have eq35289 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25043
       have i₂ := eq35267
       grind)
    | exact superpose eq35267 eq25043
    | exact resolve eq25043 eq35267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25043
  have eq35295 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq35267
       grind)
    | exact superpose eq35267 eq39
    | exact resolve eq39 eq35267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35267
  have eq35309 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq35289
  have eq35323 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35295
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35295
    | exact resolve eq35295 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35295
  have eq35336 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35309 eq27
    | exact resolve eq27 eq35309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35309
  have eq35363 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35323 eq26900
    | exact resolve eq26900 eq35323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26900 eq35323
  have eq35380 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq35363
  have eq47119 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (σ y) X0) X1) X2) = (M.op (M.op (σ x) X3) X4) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq25906 eq1650
    | (have j0 := eq1650 (σ y) X1 X2 X3 X4 x
       grind)
    | exact resolve eq1650 eq25906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47123 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (σ y) X0) X1) X2) = (M.op (M.op (σ x) X3) X4) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq29363 eq1650
    | (have j0 := eq1650 (σ y) X1 X2 X3 X4 x
       grind)
    | exact resolve eq1650 eq29363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq47576 : ∀ X3 X4 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X3) X4) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X3 X4
    first
    | (have i₁ := eq47123 x x X3 X3 X4
       have i₂ := eq16 sF3 x x X3
       grind)
    | exact superpose eq16 eq47123
    | exact resolve eq47123 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47123
  have eq47580 : ∀ X3 X4 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X3) X4) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X3 X4
    first
    | (have i₁ := eq47119 x x X3 X3 X4
       have i₂ := eq16 sF3 x x X3
       grind)
    | exact superpose eq16 eq47119
    | exact resolve eq47119 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47119
  have eq47868 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29373 eq47576
    | exact resolve eq47576 eq29373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29373 eq47576
  have eq47872 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26537 eq47580
    | exact resolve eq47580 eq26537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26537 eq47580
  have eq48067 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47868 eq47872
    | exact resolve eq47872 eq47868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47868 eq47872
  have eq48068 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq48067
  have eq48766 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48068 eq174
    | exact resolve eq174 eq48068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48805 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq48068
  have eq48861 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48766 eq25906
    | exact resolve eq25906 eq48766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25906
  have eq48865 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48766 eq29363
    | exact resolve eq29363 eq48766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29363 eq48766
  have eq48882 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq48865
  have eq48884 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq48861
  have eq48894 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq48882
       have r₂ := eq48805
       grind)
    | exact resolve eq48882 eq48805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48882
  have eq48896 : x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq48884
       have r₂ := eq48805
       grind)
    | exact resolve eq48884 eq48805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48805 eq48884
  have eq48910 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq48894 eq48896
    | exact resolve eq48896 eq48894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48894 eq48896
  have eq48911 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq48910
  have eq48938 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq48911 eq1044
    | exact resolve eq1044 eq48911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48911
  have eq49317 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq48938 eq26
    | (have j1 := eq48938 (σ y) X0
       grind)
    | exact resolve eq26 eq48938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48938
  have eq49564 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49317 eq174
    | exact resolve eq174 eq49317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq49569 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49317 eq828
    | exact resolve eq828 eq49317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49317
  have eq49660 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35380 eq49569
    | exact resolve eq49569 eq35380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35380 eq49569
  have eq51375 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49660 eq97
    | exact resolve eq97 eq49660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq51381 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49660 eq25997
    | exact resolve eq25997 eq49660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25997 eq49660
  have eq51412 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51381
  have eq51433 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq51412
       have r₂ := eq35336
       grind)
    | exact resolve eq51412 eq35336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35336 eq51412
  have eq51438 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq51375
    | exact resolve eq51375 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51375
  have eq51452 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51433 eq51438
    | exact resolve eq51438 eq51433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51438
  have eq51462 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30085 eq51452
    | exact resolve eq51452 eq30085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30085 eq51452
  have eq51471 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51433 eq51462
    | exact resolve eq51462 eq51433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51433 eq51462
  have eq51472 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq51471
  have eq52703 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51472 eq27
    | exact resolve eq27 eq51472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52744 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51472 eq49564
    | exact resolve eq49564 eq51472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49564 eq51472
  have eq52751 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq52744
  have eq53076 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq52751 eq29808
    | (have j0 := eq29808 X0
       grind)
    | exact resolve eq29808 eq52751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29808 eq52751
  have eq53096 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq53076 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53076
  have eq53107 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq53096 X0
       grind)
    | (have r₁ := eq53096 X0
       have r₂ := eq52703
       grind)
    | exact resolve eq53096 eq52703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53096
  have eq53424 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53107 eq192
    | exact resolve eq192 eq53107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq53107
  have eq53562 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq53424
    | exact resolve eq53424 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53424
  have eq53602 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30158 eq53562
    | exact resolve eq53562 eq30158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30158 eq53562
  have eq53627 : y = (M.op x y) := by
    first
    | (have r₁ := eq53602
       have r₂ := eq52703
       grind)
    | exact resolve eq53602 eq52703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52703 eq53602
  have eq53644 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq53627
       grind)
    | exact superpose eq53627 eq18
    | exact resolve eq18 eq53627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq53645 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq53627
       grind)
    | exact superpose eq53627 eq24
    | exact resolve eq24 eq53627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq53648 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq193
       have i₂ := eq53627
       grind)
    | exact superpose eq53627 eq193
    | exact resolve eq193 eq53627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq53722 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq53645 eq20
    | exact resolve eq20 eq53645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53725 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq53645 eq15
    | exact resolve eq15 eq53645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53792 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq53645 eq377
    | exact resolve eq377 eq53645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq56441 : ∀ X0 X1 X2 X3 X4 : G, (M.op y y) = (M.op (M.op x X0) X1) ∨ y = (M.op (M.op (M.op y X2) X3) X4) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10939 y X2 X3 X4 X0 X1
       have i₂ := eq27689
       grind)
    | exact superpose eq27689 eq10939
    | (have j0 := eq10939 y X2 X3 X4 X4 x
       grind)
    | exact resolve eq10939 eq27689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10939 eq27689
  have eq56753 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ y = (M.op (M.op (M.op y X2) X3) X4) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56441 X0 X1 X2 X3 X4
       have i₂ := eq53627
       grind)
    | exact superpose eq53627 eq56441
    | (have j0 := eq56441 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq56441 eq53627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56441
  have eq56839 : ∀ X0 X1 : G, y = (M.op y y) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq56753 X0 X1 x x x
       have i₂ := eq16 y x x x
       grind)
    | exact superpose eq16 eq56753
    | (have j0 := eq56753 X0 X1 x x x
       grind)
    | exact resolve eq56753 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56753
  have eq56885 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq56839 X0 X1
       have i₂ := eq53627
       grind)
    | exact superpose eq53627 eq56839
    | (have j0 := eq56839 X0 X1
       grind)
    | exact resolve eq56839 eq53627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56839
  have eq56903 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27751 eq56885
    | (have j1 := eq27751 y (M.op x y)
       grind)
    | exact resolve eq56885 eq27751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27751 eq56885
  have eq76857 : ∀ X0 : G, (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26461 eq834
    | (have j0 := eq834 X0 (σ x)
       have j1 := eq26461 (σ x)
       grind)
    | exact resolve eq834 eq26461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq76913 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq76857 X0
       have j1 := eq26461 (σ x)
       grind)
    | (have r₁ := eq76857 X0
       have r₂ := eq26461 (σ x)
       grind)
    | exact resolve eq76857 eq26461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76857
  have eq76926 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26461 eq76913
    | (have j0 := eq76913 X0
       have j1 := eq26461 (σ x)
       grind)
    | exact resolve eq76913 eq26461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26461 eq76913
  have eq76937 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26511 eq76926
    | (have j0 := eq76926 X0
       grind)
    | exact resolve eq76926 eq26511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26511 eq76926
  have eq76944 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28288 eq76937
    | (have j0 := eq76937 X0
       have j1 := eq28288 (σ x) (M.op (M.op (σ x) (σ y)) X0)
       grind)
    | exact resolve eq76937 eq28288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28288 eq76937
  have eq76950 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq76944 X0
       have j1 := eq26455 X0 (σ x)
       grind)
    | (have r₁ := eq76944 X0
       have r₂ := eq26455 (σ y) (k (M.op (M.op (σ x) (σ y)) X0) (σ x))
       grind)
    | (have r₁ := eq76944 X0
       have r₂ := eq26455 (M.op (M.op (σ x) (σ y)) X0) (σ x)
       grind)
    | (have r₁ := eq76944 X0
       have r₂ := eq26455 (σ y) (σ y)
       grind)
    | exact resolve eq76944 eq26455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26455 eq76944
  have eq76955 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f76955_14 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f76955_15 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f76955_24 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ y)) := by grind
    have f76955_25 : (σ x) ≠ (k (σ x) (σ x)) := by grind
    have f76955_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f76955_28 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) := by
      intro X0
      first
      | (have j0 := f76955_15 X0
         grind)
      | (have r₁ := f76955_15 X0
         have r₂ := f76955_26
         grind)
      | exact resolve f76955_15 f76955_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f76955_29 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f76955_14 X0
         grind)
      | (have r₁ := f76955_14 X0
         have r₂ := f76955_25
         grind)
      | exact resolve f76955_14 f76955_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f76955_30 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
      intro X0
      first
      | (have j0 := f76955_29 X0
         grind)
      | (have r₁ := f76955_29 X0
         have r₂ := f76955_26
         grind)
      | exact resolve f76955_29 f76955_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f76955_31 : (k (σ x) (σ x)) = (M.op (σ x) (σ y)) := by
      first
      | (have i₁ := f76955_30 x
         have i₂ := f76955_28 x
         grind)
      | exact superpose f76955_28 f76955_30
      | exact resolve f76955_30 f76955_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f76955_32 : False := by
      first
      | (have r₁ := f76955_31
         have r₂ := f76955_24
         grind)
      | exact resolve f76955_31 f76955_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f76955_32
  clear eq27084 eq76950
  have eq89231 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56903 eq53648
    | exact resolve eq53648 eq56903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53648 eq56903
  have eq89349 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq89231
    | exact resolve eq89231 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89231
  have eq89373 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53722 eq89349
    | exact resolve eq89349 eq53722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89349
  have eq89382 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq26258 (σ y)
       grind)
    | (have r₁ := eq89373
       have r₂ := eq26258 (σ y)
       grind)
    | exact resolve eq89373 eq26258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26258 eq89373
  have eq89406 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq89382 eq26291
    | exact resolve eq26291 eq89382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26291
  have eq89428 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq89382 eq53792
    | exact resolve eq53792 eq89382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53792
  have eq89443 : ∀ X0 X1 X2 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (M.op (σ y) X0) X1) X2) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq89382 eq10979
    | (have j0 := eq10979 (σ y) X0 X1 X2
       grind)
    | (have r₁ := eq10979 (σ y) X1 X2 x
       have r₂ := eq89382
       grind)
    | exact resolve eq10979 eq89382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10979 eq89382
  have eq89446 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (M.op (σ y) X0) X1) X2) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq89443 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89443
  have eq89453 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq89406
  have eq89463 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq89446 x x x
       have i₂ := eq16 sF3 x x x
       grind)
    | exact superpose eq16 eq89446
    | exact resolve eq89446 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89446
  have eq89478 : y = (k y (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq89428
    | exact resolve eq89428 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq89428
  have eq89489 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq89453 eq89463
    | exact resolve eq89463 eq89453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89453 eq89463
  have eq89497 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq89478
       have i₂ := eq53627
       grind)
    | exact superpose eq53627 eq89478
    | exact resolve eq89478 eq53627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53627 eq89478
  have eq89776 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq89489 eq26446
    | exact resolve eq26446 eq89489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26446 eq89489
  have eq89856 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq89776
  have eq89907 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq89856
    | exact resolve eq89856 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89856
  have eq90206 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq89497 eq918
    | (have j0 := eq918 (M.op x y)
       grind)
    | (have r₁ := eq918 (M.op x y)
       have r₂ := eq89497
       grind)
    | exact resolve eq918 eq89497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90220 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq90206
  have eq92284 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq918 x
       have i₂ := eq89907
       grind)
    | exact superpose eq89907 eq918
    | (have j0 := eq918 x
       grind)
    | (have r₁ := eq918 x
       have r₂ := eq89907
       grind)
    | exact resolve eq918 eq89907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq89907
  have eq92298 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq92284
  have eq92346 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq90220 eq179
    | exact resolve eq179 eq90220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq92407 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq90220 eq1086
    | exact resolve eq1086 eq90220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq92422 : x ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq90220
  have eq92440 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq89497 eq92407
    | (have j0 := eq92407 X0
       grind)
    | exact resolve eq92407 eq89497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89497 eq92407
  have eq92441 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq92440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92440
  have eq92470 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq92298 eq92346
    | exact resolve eq92346 eq92298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92298 eq92346
  have eq92502 : x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq92441 eq92470
    | (have j0 := eq92470 (M.op x y)
       grind)
    | exact resolve eq92470 eq92441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92441 eq92470
  have eq92521 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq92502
       have r₂ := eq92422
       grind)
    | exact resolve eq92502 eq92422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92422 eq92502
  have eq92608 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq92521 eq1044
    | exact resolve eq1044 eq92521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq92521
  have eq92782 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq92608 X0 x
       have i₂ := eq828 x
       grind)
    | exact superpose eq828 eq92608
    | (have j1 := eq828 x
       grind)
    | exact resolve eq92608 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq92968 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53644
       have i₂ := eq92608 sF0 x
       grind)
    | (have i₁ := eq53644
       have i₂ := eq92608 X0 sF0
       grind)
    | exact superpose eq92608 eq53644
    | (have j1 := eq92608 y X0
       grind)
    | exact resolve eq53644 eq92608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53644 eq92608
  have eq93093 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq92968 eq92782
    | (have j0 := eq92782 y
       grind)
    | exact resolve eq92782 eq92968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92782
  have eq93111 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92968 eq93093
    | exact resolve eq93093 eq92968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92968 eq93093
  have eq97382 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq93111
       grind)
    | exact superpose eq93111 eq39
    | exact resolve eq39 eq93111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq93111
  have eq97429 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97382
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq97382
    | exact resolve eq97382 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97382
  have eq97433 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq97429
    | exact resolve eq97429 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97429
  have eq97437 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53722 eq97433
    | exact resolve eq97433 eq53722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97433
  have eq97563 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97437 eq76955
    | exact resolve eq76955 eq97437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76955 eq97437
  have eq97586 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq97563
  have eq97643 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97586 eq27
    | exact resolve eq27 eq97586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97586
  have eq97696 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq97643
       have r₂ := eq53722
       grind)
    | exact resolve eq97643 eq53722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53722 eq97643
  have eq97863 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97696 eq53725
    | exact resolve eq53725 eq97696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53725 eq97696
  have eq97933 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq97863
    | exact resolve eq97863 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq97863
  have eq97934 : x = (M.op x y) := by grind
  clear eq97933
  have eq98021 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq97934
       grind)
    | exact superpose eq97934 eq22
    | exact resolve eq22 eq97934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq97934
  have eq98260 : (σ x) = (σ y) := by
    first
    | exact superpose eq98021 eq53645
    | exact resolve eq53645 eq98021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53645
  have eq98261 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq98021 eq20
    | exact resolve eq20 eq98021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq98021
  have eq98703 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98260 eq26
    | exact resolve eq26 eq98260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq98777 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq98260 eq22218
    | exact resolve eq22218 eq98260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22218 eq98260
  have eq100273 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq98703 eq12
    | exact resolve eq12 eq98703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98703
  have eq100318 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq100273
  have eq100356 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98777 eq100318
    | exact resolve eq100318 eq98777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98777 eq100318
  have eq100357 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq100356
  have eq100409 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq100357 eq27
    | exact resolve eq27 eq100357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq100357
  have eq100493 : False := by grind
  exact eq100493

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_pxy_y_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq66 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 (M.op X0 X1) x x X4
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X0)) = (k (M.op (M.op X0 X1) X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    grind
  have eq74 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op (M.op X0 X1) X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X1 X2
       have i₂ := eq9 X0 X1 X2 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq963 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq1023 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq963 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1039 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1023 (τ X1) X0
       grind)
    | exact superpose eq1023 eq19
    | (have j1 := eq1023 (τ X1) X0
       grind)
    | exact resolve eq19 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1043 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1023 (σ X1) (σ X0)
       grind)
    | exact superpose eq1023 eq15
    | (have j1 := eq1023 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1057 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1039
    | exact resolve eq1039 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1102 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1057 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1057
    | (have j0 := eq1057 X0 X1
       grind)
    | exact resolve eq1057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1898 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1043 x y
       grind)
    | exact superpose eq1043 eq16
    | (have j1 := eq1043 x y
       grind)
    | exact resolve eq16 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1925 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1043 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1943 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1925 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq1925
    | (have j0 := eq1925 (τ X0) (τ X1)
       grind)
    | exact resolve eq1925 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1951 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1943 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1943
    | (have j0 := eq1943 X0 X1
       grind)
    | exact resolve eq1943 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq1953 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1951 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1951
    | (have j0 := eq1951 X0 X1
       grind)
    | exact resolve eq1951 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq1954 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1953 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1953
    | (have j0 := eq1953 X0 X1
       grind)
    | exact resolve eq1953 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq1955 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1954 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1954
    | (have j0 := eq1954 X0 X1
       grind)
    | exact resolve eq1954 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq2052 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1898
       have i₂ := eq1102 y x
       grind)
    | exact superpose eq1102 eq1898
    | (have j1 := eq1102 (σ y) (σ x)
       grind)
    | (have r₁ := eq1898
       have r₂ := eq1102 y x
       grind)
    | exact resolve eq1898 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq1898
  have eq2053 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2052
  have eq2058 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ x) (σ y) X0 X1
       have i₂ := eq2053
       grind)
    | exact superpose eq2053 eq9
    | exact resolve eq9 eq2053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2083 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2058 (σ y) X0
       have i₂ := eq2053
       grind)
    | exact superpose eq2053 eq2058
    | exact resolve eq2058 eq2053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2141 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq2212 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2053
       have i₂ := eq2141 (σ y)
       grind)
    | exact superpose eq2141 eq2053
    | exact resolve eq2053 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053 eq2141
  have eq2235 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2212
  have eq2256 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2058 (σ x) x
       have i₂ := eq2235
       grind)
    | exact superpose eq2235 eq2058
    | exact resolve eq2058 eq2235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq2269 : ∀ X0 : G, (σ x) = (k (M.op (σ x) X0) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74 (σ x) (σ x) x
       have i₂ := eq2235
       grind)
    | exact superpose eq2235 eq74
    | exact resolve eq74 eq2235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235
  have eq2278 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2256 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq2585 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2269 x
       have i₂ := eq2278 x
       grind)
    | exact superpose eq2278 eq2269
    | exact resolve eq2269 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269 eq2278
  have eq2602 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2585
  have eq2614 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2602
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2602
    | exact resolve eq2602 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602
  have eq2623 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq2614
       grind)
    | exact superpose eq2614 eq10
    | exact resolve eq10 eq2614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614
  have eq2664 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2623
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2623
    | exact resolve eq2623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623
  have eq2672 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1955 x x
       have i₂ := eq2664
       grind)
    | exact superpose eq2664 eq1955
    | (have j0 := eq1955 x x
       grind)
    | (have r₁ := eq1955 x x
       have r₂ := eq2664
       grind)
    | exact resolve eq1955 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955 eq2664
  have eq2675 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq2672
  have eq2681 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x X0) X1) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x y X0 X1
       have i₂ := eq2675
       grind)
    | exact superpose eq2675 eq9
    | exact resolve eq9 eq2675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2769 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2681 y X0
       have i₂ := eq2675
       grind)
    | exact superpose eq2675 eq2681
    | exact resolve eq2681 eq2675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2681
  have eq2825 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq2769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769
  have eq2888 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2675
       have i₂ := eq2825 y
       grind)
    | exact superpose eq2825 eq2675
    | exact resolve eq2675 eq2825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2675 eq2825
  have eq2915 : x = (M.op x x) := by grind
  clear eq2888
  have eq2920 : ∀ X0 X1 : G, x = (k (M.op (M.op x X0) X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq74 x X1 x
       have i₂ := eq2915
       grind)
    | exact superpose eq2915 eq74
    | exact resolve eq74 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq2924 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x x x x
       have i₂ := eq2915
       grind)
    | exact superpose eq2915 eq9
    | exact resolve eq9 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2927 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq66 x x x
       have i₂ := eq2915
       grind)
    | exact superpose eq2915 eq66
    | exact resolve eq66 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2944 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2927 X0
       have i₂ := eq2915
       grind)
    | exact superpose eq2915 eq2927
    | exact resolve eq2927 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915 eq2927
  have eq2949 : x = (k x x) := by
    first
    | (have i₁ := eq2920 x x
       have i₂ := eq2924 x x
       grind)
    | exact superpose eq2924 eq2920
    | exact resolve eq2920 eq2924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2920 eq2924
  have eq3022 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1925 x x
       have i₂ := eq2949
       grind)
    | exact superpose eq2949 eq1925
    | (have j0 := eq1925 x x
       grind)
    | exact resolve eq1925 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925 eq2949
  have eq3027 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3022
  have eq3437 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq66 (σ x) (σ x) x
       have i₂ := eq3027
       grind)
    | exact superpose eq3027 eq66
    | exact resolve eq66 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq3456 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq3437 X0
       have i₂ := eq3027
       grind)
    | exact superpose eq3027 eq3437
    | exact resolve eq3437 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3027 eq3437
  have eq3480 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3456 (σ y)
       grind)
    | exact superpose eq3456 eq16
    | exact resolve eq16 eq3456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3456
  have eq3534 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3480
       have i₂ := eq2944 y
       grind)
    | exact superpose eq2944 eq3480
    | exact resolve eq3480 eq2944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944 eq3480
  have eq3535 : False := by grind
  exact eq3535

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_x_y_pxx_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  have eq57 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X2) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 (M.op X0 X1) x x X4
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (k (M.op (M.op X0 X1) X2) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X2) X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq216 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : ∀ X2 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x x) X2) = X2 := by
    intro X2
    first
    | exact superpose eq60 eq66
    | (have j0 := eq66 x y (M.op x y) x
       grind)
    | exact resolve eq66 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1714 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1716 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1714 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq6105 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1716 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1716
    | (have j0 := eq1716 (τ X0)
       grind)
    | exact resolve eq1716 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6113 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6105 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6105
    | (have j0 := eq6105 X0
       grind)
    | exact resolve eq6105 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6105
  have eq6119 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6113 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6113
    | (have j0 := eq6113 X0
       grind)
    | exact resolve eq6113 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq8059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq8060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq8059
    | exact resolve eq8059 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8059
  have eq8071 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq8060
       have r₂ := eq27
       grind)
    | exact resolve eq8060 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8060
  have eq8073 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq8071
    | exact resolve eq8071 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8071
  have eq8077 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8073 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq8073
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8073
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8073
       grind)
    | exact resolve eq13 eq8073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8073
  have eq8101 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq8077
  have eq8127 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8101 eq49
    | exact resolve eq49 eq8101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8101
  have eq8149 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq8127
    | exact resolve eq8127 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8127
  have eq8152 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq6119 x
       grind)
    | (have r₁ := eq8149
       have r₂ := eq6119 x
       grind)
    | exact resolve eq8149 eq6119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6119 eq8149
  have eq8153 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq216 X0
       have i₂ := eq8152
       grind)
    | exact superpose eq8152 eq216
    | exact resolve eq216 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8155 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq8152
       grind)
    | exact superpose eq8152 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq8152
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8152
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8152
       grind)
    | exact resolve eq13 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8159 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X2 X3 x x
       have i₂ := eq8152
       grind)
    | exact superpose eq8152 eq57
    | exact resolve eq57 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8152
  have eq8179 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8155
  have eq8190 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X3
    first
    | (have i₁ := eq8159 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq8159
    | exact resolve eq8159 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8159
  have eq8198 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8190 x
       have i₂ := eq216 x
       grind)
    | exact superpose eq216 eq8190
    | exact resolve eq8190 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8190
  have eq8204 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq8179
       grind)
    | exact superpose eq8179 eq43
    | exact resolve eq43 eq8179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq8179
  have eq8228 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8204
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8204
    | exact resolve eq8204 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8204
  have eq13379 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8153 eq8198
    | exact resolve eq8198 eq8153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8153 eq8198
  have eq13434 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq13379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13379
  have eq13526 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13434 y
       grind)
    | exact superpose eq13434 eq18
    | (have j1 := eq13434 y
       grind)
    | exact resolve eq18 eq13434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13434
  have eq13562 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13526
  have eq13593 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13562 eq61
    | exact resolve eq61 eq13562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq15122 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq13593
    | (have j0 := eq13593 (σ y) X0
       grind)
    | exact resolve eq13593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13593
  have eq15278 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13562 eq15122
    | exact resolve eq15122 eq13562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13562 eq15122
  have eq15345 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15278
  have eq15395 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15345
    | (have j0 := eq15345 (σ y)
       grind)
    | exact resolve eq15345 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15345
  have eq15528 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15395 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15395
       grind)
    | exact resolve eq13 eq15395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15395
  have eq15594 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15528
       have r₂ := eq8228
       grind)
    | exact resolve eq15528 eq8228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8228 eq15528
  have eq15866 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15594 eq49
    | exact resolve eq49 eq15594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq15594
  have eq15888 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq15866
    | exact resolve eq15866 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15866
  have eq16753 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq15888
       grind)
    | exact superpose eq15888 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq15888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15888
  have eq16754 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq16753
  have eq17322 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq216 X0
       have i₂ := eq16754
       grind)
    | exact superpose eq16754 eq216
    | exact resolve eq216 eq16754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17328 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X2 X3 x x
       have i₂ := eq16754
       grind)
    | exact superpose eq16754 eq57
    | exact resolve eq57 eq16754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq16754
  have eq17363 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) := by
    intro X3
    first
    | (have i₁ := eq17328 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq17328
    | exact resolve eq17328 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17328
  have eq17371 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17363 x
       have i₂ := eq216 x
       grind)
    | exact superpose eq216 eq17363
    | exact resolve eq17363 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq17363
  have eq27917 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17322 eq17371
    | exact resolve eq17371 eq17322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17322 eq17371
  have eq27993 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq27917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27917
  have eq28602 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27993 y
       grind)
    | exact superpose eq27993 eq18
    | (have j1 := eq27993 y
       grind)
    | exact resolve eq18 eq27993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27993
  have eq28653 : x = (M.op x y) := by grind
  clear eq28602
  have eq28699 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28653 eq20
    | exact resolve eq20 eq28653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq28702 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq28653 eq60
    | exact resolve eq60 eq28653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq28753 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq28653 eq1215
    | (have j0 := eq1215 X0
       grind)
    | exact resolve eq1215 eq28653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq28757 : ∀ X0 : G, (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28753
  have eq28809 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28699
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28699
    | exact resolve eq28699 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28699
  have eq30252 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq28809 eq26
    | exact resolve eq26 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq34719 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq28702 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28702
    | (have j0 := eq28702 y X0
       grind)
    | exact resolve eq28702 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28702
  have eq34899 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq28653 eq34719
    | exact resolve eq34719 eq28653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34719
  have eq35041 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq34899 y
       grind)
    | exact superpose eq34899 eq18
    | (have j1 := eq34899 y
       grind)
    | exact resolve eq18 eq34899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq34899
  have eq35083 : x = (M.op x x) := by
    first
    | exact superpose eq28653 eq35041
    | exact resolve eq35041 eq28653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28653 eq35041
  have eq35145 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28757 X0
       have i₂ := eq35083
       grind)
    | exact superpose eq35083 eq28757
    | exact resolve eq28757 eq35083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28757 eq35083
  have eq35392 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1716 x
       have i₂ := eq35145 x
       grind)
    | exact superpose eq35145 eq1716
    | (have j0 := eq1716 x
       grind)
    | exact resolve eq1716 eq35145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716 eq35145
  have eq35463 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq35392
  have eq35516 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35463
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35463
    | exact resolve eq35463 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35463
  have eq35559 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28809 eq35516
    | exact resolve eq35516 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28809 eq35516
  have eq40488 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq35559 eq62
    | exact resolve eq62 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq40545 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq35559 eq40488
    | exact resolve eq40488 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35559 eq40488
  have eq40587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40545 eq30252
    | exact resolve eq30252 eq40545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30252 eq40545
  have eq40671 : False := by grind
  exact eq40671

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_y_pyx_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  clear eq43
  have eq57 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X2) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 (M.op X0 X1) x x X4
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (k (M.op (M.op X0 X1) X2) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X2) X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq82
    | exact resolve eq82 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq86 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X0 X2) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) x
       have i₂ := eq62 X0 X1 x
       grind)
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq62 X0 X1 x
       grind)
    | exact superpose eq62 eq12
    | (have r₁ := eq12 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq62 X1 X1 (M.op X1 X1)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq62 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq497 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X2) (M.op X0 X2)) ∨ (M.op X0 X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq493 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq1307 : ∀ X2 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x x) X2) = X2 := by
    intro X2
    first
    | exact superpose eq60 eq66
    | (have j0 := eq66 x y (M.op x y) x
       grind)
    | exact resolve eq66 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq8663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8663
    | exact resolve eq8663 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8663
  have eq8675 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8664
       have r₂ := eq27
       grind)
    | exact resolve eq8664 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8664
  have eq8677 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8675
    | exact resolve eq8675 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8675
  have eq8679 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8677
    | exact resolve eq8677 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8677
  have eq8683 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8679 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8679
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8679
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8679
       grind)
    | exact resolve eq12 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8679
  have eq8714 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8683
       have r₂ := eq26
       grind)
    | exact resolve eq8683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8683
  have eq8721 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8714
    | exact resolve eq8714 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8714
  have eq8722 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq8721
  have eq8729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8722 eq87
    | exact resolve eq87 eq8722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq8722
  have eq8737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8729
  have eq8739 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8737
       have r₂ := eq27
       grind)
    | exact resolve eq8737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8737
  have eq8743 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq8739
       grind)
    | exact superpose eq8739 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8739
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8739
       grind)
    | exact resolve eq12 eq8739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8739
  have eq8774 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8743
       have r₂ := eq18
       grind)
    | exact resolve eq8743 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8743
  have eq8781 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8774
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8774
    | exact resolve eq8774 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8774
  have eq8782 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8781
  have eq8785 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq8782
       grind)
    | exact superpose eq8782 eq44
    | exact resolve eq44 eq8782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq8782
  have eq8799 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8785
    | exact resolve eq8785 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8785
  have eq8812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8799 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq8799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8812
    | exact resolve eq8812 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8812
  have eq8826 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8815
       have r₂ := eq27
       grind)
    | exact resolve eq8815 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8815
  have eq8828 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8826
    | exact resolve eq8826 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8826
  have eq8830 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8828
    | exact resolve eq8828 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8828
  have eq8831 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8830
  have eq8835 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8831 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8831
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8831
       grind)
    | exact resolve eq12 eq8831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8831
  have eq8866 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8835
       have r₂ := eq26
       grind)
    | exact resolve eq8835 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8835
  have eq8873 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8866
    | exact resolve eq8866 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8866
  have eq8874 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8873
  have eq8889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8874 eq8799
    | exact resolve eq8799 eq8874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8799 eq8874
  have eq8891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8889
  have eq8895 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8891
       have r₂ := eq27
       grind)
    | exact resolve eq8891 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8891
  have eq8899 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8895 eq61
    | exact resolve eq61 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq12194 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq8899
    | (have j0 := eq8899 (σ y) X0
       grind)
    | exact resolve eq8899 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8899
  have eq12354 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8895 eq12194
    | exact resolve eq12194 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12194
  have eq12391 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12354 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12354
  have eq12491 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12391
    | (have j0 := eq12391 (σ y)
       grind)
    | exact resolve eq12391 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12391
  have eq12617 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12491 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12491
       grind)
    | exact resolve eq13 eq12491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12491
  have eq12675 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12617
       have r₂ := eq8895
       grind)
    | exact resolve eq12617 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895 eq12617
  have eq13074 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12675 eq49
    | exact resolve eq49 eq12675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq12675
  have eq13095 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq13074
    | exact resolve eq13074 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13074
  have eq14031 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110 x
       have i₂ := eq13095
       grind)
    | exact superpose eq13095 eq110
    | (have j0 := eq110 x
       grind)
    | exact resolve eq110 eq13095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13095
  have eq14037 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq14031
  have eq14197 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq213 X0
       have i₂ := eq14037
       grind)
    | exact superpose eq14037 eq213
    | exact resolve eq213 eq14037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14203 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X2 X3 x x
       have i₂ := eq14037
       grind)
    | exact superpose eq14037 eq57
    | exact resolve eq57 eq14037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq14037
  have eq14237 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) := by
    intro X3
    first
    | (have i₁ := eq14203 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq14203
    | exact resolve eq14203 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14203
  have eq14245 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14237 x
       have i₂ := eq213 x
       grind)
    | exact superpose eq213 eq14237
    | exact resolve eq14237 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq14237
  have eq24872 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14197 eq14245
    | exact resolve eq14245 eq14197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14197 eq14245
  have eq24961 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24872 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24872
  have eq25082 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24961 y
       grind)
    | exact superpose eq24961 eq18
    | (have j1 := eq24961 y
       grind)
    | exact resolve eq18 eq24961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24961
  have eq25133 : x = (M.op x y) := by grind
  clear eq25082
  have eq25172 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq25133 eq20
    | exact resolve eq20 eq25133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25175 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq25133 eq60
    | exact resolve eq60 eq25133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq25226 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq25133 eq1307
    | (have j0 := eq1307 X0
       grind)
    | exact resolve eq1307 eq25133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq25228 : ∀ X0 : G, (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25226 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25226
  have eq25280 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25172
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25172
    | exact resolve eq25172 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25172
  have eq25295 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq25280 eq26
    | exact resolve eq26 eq25280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq26054 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op x x)
       have i₂ := eq25228 (τ X0)
       grind)
    | exact superpose eq25228 eq38
    | exact resolve eq38 eq25228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq25228
  have eq26072 : ∀ X0 : G, (k (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26054 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq26054
    | exact resolve eq26054 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26054
  have eq27431 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq25175 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25175
    | (have j0 := eq25175 y X0
       grind)
    | exact resolve eq25175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25175
  have eq27609 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq25133 eq27431
    | exact resolve eq27431 eq25133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27431
  have eq27753 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27609 y
       grind)
    | exact superpose eq27609 eq18
    | (have j1 := eq27609 y
       grind)
    | exact resolve eq18 eq27609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq27609
  have eq27802 : x = (M.op x x) := by
    first
    | exact superpose eq25133 eq27753
    | exact resolve eq27753 eq25133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25133 eq27753
  have eq27854 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26072 X0
       have i₂ := eq27802
       grind)
    | exact superpose eq27802 eq26072
    | exact resolve eq26072 eq27802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26072 eq27802
  have eq27924 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27854 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27854
    | (have j0 := eq27854 X0
       grind)
    | exact resolve eq27854 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq27854
  have eq27942 : ∀ X0 : G, (k (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq25280 eq27924
    | exact resolve eq27924 eq25280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25280 eq27924
  have eq29074 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27942 eq110
    | (have j0 := eq110 (σ (M.op x y))
       grind)
    | exact resolve eq110 eq27942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq29130 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq29074
  have eq30534 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq29130 eq497
    | exact resolve eq497 eq29130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq29130
  have eq30556 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq27942 eq30534
    | (have j0 := eq30534 X0
       grind)
    | exact resolve eq30534 eq27942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27942 eq30534
  have eq30557 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq30556 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30556
  have eq30665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30557 eq25295
    | exact resolve eq25295 eq30557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25295 eq30557
  have eq30748 : False := by grind
  exact eq30748

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation4079 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq64 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq10
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq104 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (σ X0) X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (σ X0) X1 X2 X3
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 X0)) = (M.op (M.op (M.op (τ X0) X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (τ X0) X1 X2 X3
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq108 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X2 x
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 (M.op X0 X1) x x X4
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq110 X0 X1 X5
       have i₂ := eq9 (M.op X0 X1) X2 X3 X4
       grind)
    | exact superpose eq9 eq110
    | exact resolve eq110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (σ X0) X4) X5) X6) = (σ (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq104 X0 X4 X5 X6
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq104
    | exact resolve eq104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (σ (M.op X0 X2)) X3) X4) X5) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104 (M.op X0 X2) X3 X4 X5
       have i₂ := eq110 X0 X2 X1
       grind)
    | (have i₁ := eq104 (M.op X0 X0) X1 X2 X3
       have i₂ := eq110 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq110 eq104
    | exact resolve eq104 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq489 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (σ (M.op (M.op (M.op (τ X0) X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq105 X0 X1 X2 X3
       grind)
    | exact superpose eq105 eq11
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1020 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op (M.op (τ (σ X0)) X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0
       have i₂ := eq489 (σ X0) X1 X2 X3
       grind)
    | exact superpose eq489 eq23
    | exact resolve eq23 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq1054 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1020 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1020
    | exact resolve eq1020 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1840 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1847 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1840 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq1840
    | (have j0 := eq1840 X0 X1
       grind)
    | exact resolve eq1840 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq4961 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (σ (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) = (M.op (M.op (M.op (σ (M.op X0 X0)) X5) X6) X7) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq104 (M.op X0 X0) X5 X6 X7
       have i₂ := eq151 X0 X1 X2 X3 X4 (M.op X0 X0)
       grind)
    | exact superpose eq151 eq104
    | exact resolve eq104 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq151
  have eq5007 : ∀ X0 X1 X2 X3 X4 X7 : G, (σ (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) = (M.op (σ (M.op X0 X0)) X7) := by
    intro X0 X1 X2 X3 X4 X7
    first
    | (have i₁ := eq4961 X0 X1 X2 X3 X4 x x X7
       have i₂ := eq108 X0 x x
       grind)
    | exact superpose eq108 eq4961
    | exact resolve eq4961 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq4961
  have eq7561 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1847 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq1847
    | (have j0 := eq1847 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq1847 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq57414 : ∀ X0 X1 X2 X3 X4 X8 : G, (σ (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) = (σ (M.op (M.op X0 X0) X8)) := by
    intro X0 X1 X2 X3 X4 X8
    first
    | (have i₁ := eq223 X0 X8 X1 x x x
       have i₂ := eq222 (M.op X0 X1) X2 X3 X4 x x x
       grind)
    | exact superpose eq222 eq223
    | exact resolve eq223 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq223
  have eq422872 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq7561 x y
       grind)
    | exact superpose eq7561 eq16
    | (have j1 := eq7561 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq7561 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq7561 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq7561 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq7561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7561
  have eq423158 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq422872
  have eq739326 : (M.op y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq423158
       grind)
    | exact superpose eq423158 eq10
    | exact resolve eq10 eq423158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423158
  have eq739552 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq739326
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq739326
    | exact resolve eq739326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739326
  have eq739553 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq739552
  have eq739955 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) X3) = (σ (M.op (M.op (M.op x X0) X1) X2)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5007 y y X2 X3 x x
       have i₂ := eq739553
       grind)
    | exact superpose eq739553 eq5007
    | exact resolve eq5007 eq739553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5007
  have eq739993 : ∀ X0 X1 X2 X3 : G, (σ (M.op x X3)) = (σ (M.op (M.op (M.op x X0) X1) X2)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57414 y y X2 X3 x x
       have i₂ := eq739553
       grind)
    | exact superpose eq739553 eq57414
    | exact resolve eq57414 eq739553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57414 eq739553
  have eq740055 : ∀ X3 : G, (σ (M.op x x)) = (σ (M.op x X3)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X3
    first
    | (have i₁ := eq739993 x x x X3
       have i₂ := eq1054 x x x x
       grind)
    | exact superpose eq1054 eq739993
    | exact resolve eq739993 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739993
  have eq740062 : ∀ X3 : G, (M.op (σ x) X3) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X3
    first
    | (have i₁ := eq739955 x x x X3
       have i₂ := eq1054 x x x x
       grind)
    | exact superpose eq1054 eq739955
    | exact resolve eq739955 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq739955
  have eq760204 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq740062 (σ y)
       grind)
    | exact superpose eq740062 eq16
    | exact resolve eq16 eq740062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740062
  have eq761391 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq760204
       have r₂ := eq740055 y
       grind)
    | exact resolve eq760204 eq740055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740055 eq760204
  have eq761835 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq761391
       grind)
    | exact superpose eq761391 eq10
    | exact resolve eq10 eq761391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761391
  have eq762045 : x = y ∨ x = y := by
    first
    | (have i₁ := eq761835
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq761835
    | exact resolve eq761835 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761835
  have eq762046 : x = y := by grind
  clear eq762045
  have eq765735 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq762046
       grind)
    | exact superpose eq762046 eq16
    | exact resolve eq16 eq762046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762046
  have eq765736 : False := by grind
  exact eq765736

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation4111 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4111 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x x
       have i₂ := eq9 X1 x x x
       grind)
    | (have i₁ := eq9 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq9 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq29 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq29 X0 X1
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq31 (σ X1) (σ X0)
       grind)
    | exact superpose eq31 eq15
    | (have j1 := eq31 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29
  have eq325 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq31 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33
  have eq5089 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq325 x y
       grind)
    | exact superpose eq325 eq16
    | (have j1 := eq325 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq325 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq325 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq325 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq5106 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq5089
  have eq8301 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5106
       grind)
    | exact superpose eq5106 eq10
    | exact resolve eq10 eq5106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106
  have eq8319 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8301
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8301
    | exact resolve eq8301 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8301
  have eq8320 : x = y := by grind
  clear eq8319
  have eq15626 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8320
       grind)
    | exact superpose eq8320 eq16
    | exact resolve eq16 eq8320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8320
  have eq15627 : False := by grind
  exact eq15627

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation4111 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X1 (M.op x x) x X4
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | (have i₁ := eq16 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq16 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (k X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq181 X0 X1 X4
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq181
    | exact resolve eq181 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq205 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq182 X1 X0
       grind)
    | (have i₁ := eq174 X1
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq174
    | exact resolve eq174 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq221 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq205 X1 X0
       grind)
    | exact superpose eq205 eq174
    | exact resolve eq174 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq205 X0 (σ X1)
       grind)
    | exact superpose eq205 eq10
    | exact resolve eq10 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (k X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq221 (σ X1) X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq221 X0 (σ X1)
       grind)
    | exact superpose eq221 eq10
    | exact resolve eq10 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (k y y) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115
       have i₂ := eq221 sF3 x
       grind)
    | (have i₁ := eq115
       have i₂ := eq221 X0 sF3
       grind)
    | exact superpose eq221 eq115
    | exact resolve eq115 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq275 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq225 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq225
    | exact resolve eq225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq610 : ∀ X0 X1 X3 : G, (k X3 X3) = (M.op (k X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq205 x X3
       have i₂ := eq184 X0 x X1
       grind)
    | (have i₁ := eq205 (k X0 X0) X1
       have i₂ := eq184 X0 X1 (k X0 X0)
       grind)
    | exact superpose eq184 eq205
    | exact resolve eq205 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq205
  have eq927 : ∀ X0 X1 X3 : G, (k X1 X1) = (M.op (σ (k X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq610 x X3 X1
       have i₂ := eq249 x X0
       grind)
    | exact superpose eq249 eq610
    | exact resolve eq610 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq1148 : ∀ X0 X1 : G, (τ (k (σ x) (M.op X0 X0))) = (k x (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ (k X1 X1))
       have i₂ := eq275 X1 X0
       grind)
    | exact superpose eq275 eq44
    | exact resolve eq44 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq275
  have eq1159 : ∀ X0 X1 : G, (k x (τ (M.op X0 X0))) = (k x (σ (k X1 X1))) := by
    intro X0 X1
    first
    | exact superpose eq90 eq1148
    | exact resolve eq1148 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1148
  have eq1177 : ∀ X0 X1 : G, (k x (τ (k X0 X0))) = (k x (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1159 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq1159
    | exact resolve eq1159 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1184 : ∀ X1 : G, (k x (k y y)) = (k x (σ (k X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq1177 x X1
       have i₂ := eq255 x
       grind)
    | exact superpose eq255 eq1177
    | exact resolve eq1177 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1583 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1584 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1583 X0
       have j1 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq1583 x
       have r₂ := eq13 (M.op x x) x
       grind)
    | (have r₁ := eq1583 X0
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq1583 X0
       have r₂ := eq13 (M.op X0 X0) (k X0 (M.op X0 X0))
       grind)
    | exact resolve eq1583 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1591 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1584 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq1584
    | exact resolve eq1584 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1584
  have eq1610 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1613 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1619 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1613
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1613
    | exact resolve eq1613 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613
  have eq1622 : (M.op x y) = (k y x) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1610
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1610
    | exact resolve eq1610 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq1651 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1591 X0
       have i₂ := eq249 X0 X1
       grind)
    | exact superpose eq249 eq1591
    | exact resolve eq1591 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq1591
  have eq5272 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1622
       grind)
    | exact superpose eq1622 eq39
    | exact resolve eq39 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq5273 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq5272
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5272
    | exact resolve eq5272 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5272
  have eq5275 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq20 eq5273
    | exact resolve eq5273 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273
  have eq78578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq5275 eq1619
    | exact resolve eq1619 eq5275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619 eq5275
  have eq78586 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq78578
       have r₂ := eq27
       grind)
    | exact resolve eq78578 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78578
  have eq78606 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq78586 eq255
    | exact resolve eq255 eq78586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq78586
  have eq78795 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq78606
    | exact resolve eq78606 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78606
  have eq78796 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq78795
  have eq78830 : ∀ X0 : G, x = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq221 X0 y
       have i₂ := eq78796
       grind)
    | exact superpose eq78796 eq221
    | exact resolve eq221 eq78796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq78851 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ x) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq927 y X0 X1
       have i₂ := eq78796
       grind)
    | exact superpose eq78796 eq927
    | exact resolve eq927 eq78796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq78880 : (k x x) = (k x (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1184 y
       have i₂ := eq78796
       grind)
    | exact superpose eq78796 eq1184
    | exact resolve eq1184 eq78796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq78890 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1651 y x
       have i₂ := eq78796
       grind)
    | exact superpose eq78796 eq1651
    | exact resolve eq1651 eq78796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651 eq78796
  have eq79028 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq78890 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78890
    | (have j0 := eq78890 X0
       grind)
    | exact resolve eq78890 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78890
  have eq79035 : (k x x) = (k x (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq78880
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78880
    | exact resolve eq78880 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78880
  have eq79055 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ x) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq78851 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78851
    | (have j0 := eq78851 X0 X1
       grind)
    | exact resolve eq78851 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78851
  have eq79113 : x = (k x (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq78830 eq79035
    | exact resolve eq79035 eq78830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79035
  have eq79125 : ∀ X1 : G, x = (M.op (σ x) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq78830 eq79055
    | exact resolve eq79055 eq78830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78830 eq79055
  have eq79160 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq79028 eq79113
    | exact resolve eq79113 eq79028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79028 eq79113
  have eq79187 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq79160 eq31
    | exact resolve eq31 eq79160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79280 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq79187
    | exact resolve eq79187 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79187
  have eq79281 : x = (σ x) ∨ x = y := by grind
  clear eq79280
  have eq79283 : (M.op x y) = (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq79281
       grind)
    | exact superpose eq79281 eq18
    | exact resolve eq18 eq79281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84498 : x = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq79125 eq26
    | (have j1 := eq79125 (σ y)
       grind)
    | exact resolve eq26 eq79125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84499 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq79125 eq79283
    | exact resolve eq79283 eq79125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79125 eq79283
  have eq84523 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq84499
  have eq84537 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq79160 eq84498
    | exact resolve eq84498 eq79160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79160 eq84498
  have eq84556 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq84537 eq27
    | exact resolve eq27 eq84537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84537
  have eq84940 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq84523 eq31
    | exact resolve eq31 eq84523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84523
  have eq85075 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq84940
    | exact resolve eq84940 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84940
  have eq85076 : x = (M.op x y) ∨ x = y := by grind
  clear eq85075
  have eq85101 : (M.op x y) = (σ x) ∨ y = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq85076
       have i₂ := eq79281
       grind)
    | exact superpose eq79281 eq85076
    | exact resolve eq85076 eq79281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85103 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq85076
       grind)
    | exact superpose eq85076 eq22
    | exact resolve eq22 eq85076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85119 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq79281
       have i₂ := eq85076
       grind)
    | exact superpose eq85076 eq79281
    | exact resolve eq79281 eq85076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85125 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq85103
    | exact resolve eq85103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85103
  have eq85126 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq85119 eq85101
    | exact resolve eq85101 eq85119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85101 eq85119
  have eq85127 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq85126
  have eq85142 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq85125 eq84556
    | (have r₁ := eq84556
       have r₂ := eq85125
       grind)
    | exact resolve eq84556 eq85125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84556 eq85125
  have eq85143 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq85142
  have eq85144 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq85143
  have eq85145 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq85127 eq85144
    | exact resolve eq85144 eq85127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85144
  have eq85164 : x = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq85127 eq29
    | exact resolve eq29 eq85127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq85207 : (σ x) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq79281 eq85164
    | exact resolve eq85164 eq79281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79281 eq85164
  have eq85220 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq85127 eq85207
    | exact resolve eq85207 eq85127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85127 eq85207
  have eq85235 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq85145 eq31
    | exact resolve eq31 eq85145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq85145
  have eq85344 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq85220 eq85235
    | exact resolve eq85235 eq85220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85220 eq85235
  have eq85476 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq85344
  have eq85477 : x = y := by
    first
    | (have r₁ := eq85476
       have r₂ := eq85076
       grind)
    | exact resolve eq85476 eq85076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85076 eq85476
  have eq85538 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq85477
       grind)
    | exact superpose eq85477 eq18
    | exact resolve eq18 eq85477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq85539 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq85477
       grind)
    | exact superpose eq85477 eq24
    | exact resolve eq24 eq85477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq85477
  have eq85612 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq85539
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85539
    | exact resolve eq85539 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85539
  have eq85613 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq85538
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq85538
    | exact resolve eq85538 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85538
  have eq85616 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq85612 eq26
    | exact resolve eq26 eq85612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq85612
  have eq85704 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq85616
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq85616
    | exact resolve eq85616 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq85616
  have eq85714 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq85613
       grind)
    | exact superpose eq85613 eq39
    | exact resolve eq39 eq85613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq85613
  have eq85962 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq85714
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85714
    | exact resolve eq85714 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq85714
  have eq86018 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq85704 eq85962
    | exact resolve eq85962 eq85704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85704 eq85962
  have eq86061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq86018
    | exact resolve eq86018 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq86018
  have eq86079 : False := by grind
  exact eq86079

/-- `Equation4120`: `x ◇ y = ((x ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyy_x_pxy_y_pxy_Equation4120 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4120 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4120.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X0) X1) X0) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 X0) X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  clear eq37
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
  have eq182 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq41
    | exact resolve eq41 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq394 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq393
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq393
    | exact resolve eq393 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq396 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq394
    | exact resolve eq394 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq396 eq183
    | exact resolve eq183 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq396
  have eq492 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq485
       have r₂ := eq27
       grind)
    | exact resolve eq485 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq577 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq28 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq28 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq492 eq13
    | exact resolve eq13 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq584 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq582
  have eq588 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq585
       have i₂ := eq584 y
       grind)
    | exact superpose eq584 eq585
    | exact resolve eq585 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq594 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq577 X0 X1
       have i₂ := eq584 X1
       grind)
    | exact superpose eq584 eq577
    | (have j0 := eq577 X0 X1
       grind)
    | (have r₁ := eq577 X0 X0
       have r₂ := eq584 X0
       grind)
    | exact resolve eq577 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq603 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq584 X1
       grind)
    | exact superpose eq584 eq594
    | (have j0 := eq594 X0 X1
       grind)
    | exact resolve eq594 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq609 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq609 X0
       have i₂ := eq584 (M.op X0 X0)
       grind)
    | exact superpose eq584 eq609
    | (have j0 := eq609 X0
       grind)
    | exact resolve eq609 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq614 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) (k X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq610 X0
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq610
    | (have j0 := eq610 X0
       grind)
    | exact resolve eq610 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq619 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) (k X0 X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq614 X0
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq614
    | (have j0 := eq614 X0
       grind)
    | exact resolve eq614 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq620 : (τ (σ x)) = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq588 eq116
    | exact resolve eq116 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq588
  have eq627 : x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq620
    | exact resolve eq620 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq620
  have eq628 : x = (k y y) := by grind
  clear eq627
  have eq635 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq628
       grind)
    | exact superpose eq628 eq41
    | exact resolve eq41 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq635
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq635
    | exact resolve eq635 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq641 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq638
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq638
    | exact resolve eq638 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq732 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (k X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq16
    | exact resolve eq16 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq732 y X0
       have i₂ := eq628
       grind)
    | exact superpose eq628 eq732
    | exact resolve eq732 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq641 eq732
    | exact resolve eq732 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq844 : (M.op y x) = (M.op (k x x) y) := by
    first
    | (have i₁ := eq817 x
       have i₂ := eq584 x
       grind)
    | exact superpose eq584 eq817
    | exact resolve eq817 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : (M.op x y) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq817 x
       grind)
    | exact superpose eq817 eq16
    | exact resolve eq16 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq851 : (M.op x y) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq846
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq846
    | exact resolve eq846 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq868 : (M.op x y) = (k (M.op y x) x) ∨ (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq28 (M.op y x) x
       have i₂ := eq851
       grind)
    | exact superpose eq851 eq28
    | (have j0 := eq28 (M.op y x) x
       grind)
    | exact resolve eq28 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : (M.op x y) = (k (M.op y x) x) ∨ (k x x) = (M.op y x) := by
    first
    | (have i₁ := eq868
       have i₂ := eq584 x
       grind)
    | exact superpose eq584 eq868
    | exact resolve eq868 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq890 : (M.op (σ y) (σ x)) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq821 sF2
       have i₂ := eq584 sF2
       grind)
    | exact superpose eq584 eq821
    | exact resolve eq821 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq821 eq16
    | exact resolve eq16 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq898 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq26 eq892
    | exact resolve eq892 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq917 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq898
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq898
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq898 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq917
       have i₂ := eq584 sF2
       grind)
    | exact superpose eq584 eq917
    | exact resolve eq917 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq1021 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ x)) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq925 eq28
    | (have j0 := eq28 (k (σ y) (σ x)) (σ x)
       grind)
    | exact resolve eq28 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq1022 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ x)) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1021
       have i₂ := eq584 sF2
       grind)
    | exact superpose eq584 eq1021
    | exact resolve eq1021 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1048 : (σ (M.op x y)) = (k (σ (M.op y x)) (σ x)) ∨ (k x x) = (M.op y x) := by
    first
    | (have i₁ := eq40 (M.op y x)
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq40
    | exact resolve eq40 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq1049 : (σ (M.op x y)) = (k (σ (M.op y x)) (σ x)) ∨ (k x x) = (M.op y x) := by
    first
    | exact superpose eq20 eq1048
    | exact resolve eq1048 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1083 : (σ (M.op x y)) = (k (σ (k y x)) (σ x)) ∨ (k x x) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1049
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq1049
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq1049 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1049
  have eq1090 : (σ (M.op x y)) = (k (k (σ y) (σ x)) (σ x)) ∨ (k x x) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1083
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq1083
    | exact resolve eq1083 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1093 : (σ (M.op x y)) = (k (k (σ y) (σ x)) (σ x)) ∨ (k x x) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1090
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1090
    | exact resolve eq1090 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1094 : (σ (M.op x y)) = (k (k (σ y) (σ x)) (σ x)) ∨ y = (k x x) ∨ (k x x) = (k y x) := by
    first
    | (have i₁ := eq1093
       have i₂ := eq584 x
       grind)
    | exact superpose eq584 eq1093
    | exact resolve eq1093 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (k x x) = (k y x) := by
    first
    | exact superpose eq1094 eq1022
    | exact resolve eq1022 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq1094
  have eq1488 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (k x x) = (k y x) := by
    first
    | (have r₁ := eq1484
       have r₂ := eq27
       grind)
    | exact resolve eq1484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1669 : (k x x) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq619 y
       have i₂ := eq628
       grind)
    | exact superpose eq628 eq619
    | exact resolve eq619 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1673 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq641 eq619
    | exact resolve eq619 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq1703 : (k x x) ≠ (M.op x x) ∨ (M.op x y) = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1669
       grind)
    | exact superpose eq1669 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq1707 : (M.op x y) = (k x y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq1703
       have r₂ := eq584 x
       grind)
    | exact resolve eq1703 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq1712 : (M.op x y) = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1707
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1707
    | exact resolve eq1707 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq1717 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1712
       grind)
    | exact superpose eq1712 eq41
    | exact resolve eq41 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1712
  have eq1719 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1717
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1717
    | exact resolve eq1717 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1721 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq20 eq1719
    | exact resolve eq1719 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq1751 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq1673 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq1755 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq1751
       have r₂ := eq584 (σ x)
       grind)
    | exact resolve eq1751 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq1760 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1755
    | exact resolve eq1755 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq1763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq1760 eq1721
    | exact resolve eq1721 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721 eq1760
  have eq1775 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have r₁ := eq1763
       have r₂ := eq27
       grind)
    | exact resolve eq1763 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq1825 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq1775 eq91
    | exact resolve eq91 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1775
  have eq1830 : y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq32 eq1825
    | exact resolve eq1825 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq1831 : y = (k x y) := by grind
  clear eq1830
  have eq1843 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq1831
       grind)
    | exact superpose eq1831 eq36
    | exact resolve eq36 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1846 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1843
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1843
    | exact resolve eq1843 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq2775 : (k y x) = (τ (k (σ x) (σ x))) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (k x x) = (k y x) := by
    first
    | exact superpose eq1488 eq115
    | exact resolve eq115 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1488
  have eq2798 : (k x x) = (k y x) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (k x x) = (k y x) := by
    first
    | exact superpose eq98 eq2775
    | exact resolve eq2775 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq2799 : (k x x) = (k y x) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by grind
  clear eq2798
  have eq2811 : (σ (k x x)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2799
       grind)
    | exact superpose eq2799 eq40
    | exact resolve eq40 eq2799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2812 : (k x x) ≠ (k x x) ∨ y = (k x x) ∨ (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq603 y x
       have i₂ := eq2799
       grind)
    | exact superpose eq2799 eq603
    | (have j0 := eq603 y x
       grind)
    | (have r₁ := eq603 y x
       have r₂ := eq2799
       grind)
    | exact resolve eq603 eq2799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799
  have eq2813 : (k x x) ≠ (k x x) ∨ y = (k x x) ∨ (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq2812
  have eq2814 : y = (k x x) ∨ (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq2813
  have eq2820 : y = (M.op x y) ∨ y = (k x x) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2814
       have i₂ := eq1831
       grind)
    | exact superpose eq1831 eq2814
    | exact resolve eq2814 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831 eq2814
  have eq2821 : (σ (k x x)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2811
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2811
    | exact resolve eq2811 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811
  have eq2824 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2820
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2820
    | exact resolve eq2820 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2820
  have eq2825 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2821
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq2821
    | exact resolve eq2821 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821
  have eq2827 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2825
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2825
    | exact resolve eq2825 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2825
  have eq2830 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2824 eq98
    | exact resolve eq98 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq2865 : y = (k x x) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq2830
    | exact resolve eq2830 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2830
  have eq2866 : y = (k x x) ∨ y = (M.op x y) := by grind
  clear eq2865
  have eq2876 : (M.op y y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq844
       have i₂ := eq2866
       grind)
    | exact superpose eq2866 eq844
    | exact resolve eq844 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq2906 : (k y y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2876
       have i₂ := eq584 y
       grind)
    | exact superpose eq584 eq2876
    | exact resolve eq2876 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2876
  have eq2912 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2906
       have i₂ := eq628
       grind)
    | exact superpose eq628 eq2906
    | exact resolve eq2906 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq2906
  have eq2972 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq851
       have i₂ := eq2912
       grind)
    | exact superpose eq2912 eq851
    | exact resolve eq851 eq2912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq2912
  have eq3004 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2972
       have i₂ := eq584 x
       grind)
    | exact superpose eq584 eq2972
    | exact resolve eq2972 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2972
  have eq3206 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2866
       have i₂ := eq3004
       grind)
    | exact superpose eq3004 eq2866
    | exact resolve eq2866 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866 eq3004
  have eq3221 : y = (M.op x y) := by grind
  clear eq3206
  have eq3234 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3221
       grind)
    | exact superpose eq3221 eq24
    | exact resolve eq24 eq3221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3305 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3234 eq20
    | exact resolve eq20 eq3234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3234
  have eq6538 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq2827 eq603
    | (have j0 := eq603 (σ y) (σ x)
       grind)
    | (have r₁ := eq603 (σ y) (σ x)
       have r₂ := eq2827
       grind)
    | exact resolve eq603 eq2827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq2827
  have eq6539 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x x) := by grind
  clear eq6538
  have eq6540 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x x) := by grind
  clear eq6539
  have eq6547 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq1846 eq6540
    | exact resolve eq6540 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq6540
  have eq6560 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq26 eq6547
    | exact resolve eq6547 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6547
  have eq6568 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq6560
       have i₂ := eq3221
       grind)
    | exact superpose eq3221 eq6560
    | exact resolve eq6560 eq3221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6560
  have eq6572 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq6568 eq98
    | exact resolve eq98 eq6568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq6568
  have eq6612 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq32 eq6572
    | exact resolve eq6572 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6572
  have eq6621 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq6612
       have i₂ := eq3221
       grind)
    | exact superpose eq3221 eq6612
    | exact resolve eq6612 eq3221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221 eq6612
  have eq6622 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6621
  have eq6648 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6622
       grind)
    | exact superpose eq6622 eq40
    | exact resolve eq40 eq6622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq6622
  have eq6666 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6648
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6648
    | exact resolve eq6648 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6648
  have eq6681 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq6666
    | exact resolve eq6666 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6666
  have eq6691 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3305 eq6681
    | exact resolve eq6681 eq3305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6681
  have eq6703 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6691 eq890
    | exact resolve eq890 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq6740 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6703
       have i₂ := eq584 sF3
       grind)
    | exact superpose eq584 eq6703
    | exact resolve eq6703 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6703
  have eq6750 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq641 eq6740
    | exact resolve eq6740 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq6740
  have eq6772 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6750 eq898
    | exact resolve eq898 eq6750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq6750
  have eq6814 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6772
       have i₂ := eq584 sF2
       grind)
    | exact superpose eq584 eq6772
    | exact resolve eq6772 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq6772
  have eq6826 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6691 eq6814
    | exact resolve eq6814 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6691 eq6814
  have eq6827 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6826
  have eq6831 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq6827 eq27
    | exact resolve eq27 eq6827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6827
  have eq6857 : False := by grind
  exact eq6857
