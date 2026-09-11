import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pyx_Equation3607 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3607 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X2) X0)) := by
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
  have eq174 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op (M.op x y) X0)) := by
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
  have eq175 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X3) X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op (M.op X1 X3) X0)
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) X2) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X1 (M.op X2 X3)) X0) X2 X3
       have i₂ := eq16 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op x y)) X0) x) = (M.op y (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op (M.op X1 sF0) X0)
       have i₂ := eq16 X0 X1 sF0
       grind)
    | exact superpose eq16 eq174
    | exact resolve eq174 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (σ y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X1 sF4) X0)
       have i₂ := eq16 X0 X1 sF4
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ x))) = (σ (k X0 (k y x))) := by
    intro X0
    first
    | exact superpose eq114 eq38
    | exact resolve eq38 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq114
  have eq533 : ∀ X0 : G, (M.op y (M.op x (M.op X0 (M.op x y)))) = (M.op (M.op y (M.op (M.op x y) X0)) x) := by
    intro X0
    first
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op x y))) = (M.op X0 (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 (M.op x y)) X0)) = (M.op x (M.op (M.op y (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq538 : ∀ X0 : G, (M.op y (M.op x (M.op X0 (M.op x y)))) = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq174 eq533
    | exact resolve eq533 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq554 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq960 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq980 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq985 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq985 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq988 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq960 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq990 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq988 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq988 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq988 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq991 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq986 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq986
    | (have j0 := eq986 (σ X0)
       grind)
    | exact resolve eq986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq993 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq990 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq990
    | (have j0 := eq990 (σ X0) X1
       grind)
    | exact resolve eq990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1846 : ∀ X0 X1 : G, (M.op x (M.op (M.op y (M.op X1 X0)) (M.op x y))) = (M.op X1 (M.op y (M.op x (M.op X0 (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X1 (M.op y (M.op X1 X0))
       have i₂ := eq535 X1 X0
       grind)
    | (have i₁ := eq535 x (M.op X1 (M.op x y))
       have i₂ := eq535 X0 X1
       grind)
    | exact superpose eq535 eq535
    | exact resolve eq535 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1855 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq174 eq535
    | exact resolve eq535 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1883 : ∀ X0 X1 : G, (M.op x (M.op (M.op y (M.op X1 X0)) (M.op x y))) = (M.op X1 (M.op (M.op X0 x) x)) := by
    intro X0 X1
    first
    | exact superpose eq538 eq1846
    | exact resolve eq1846 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq1846
  have eq1887 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) x)) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1883 y x
       have i₂ := eq536 sF0 y x
       grind)
    | (have i₁ := eq1883 X1 X0
       have i₂ := eq536 X0 X1 sF0
       grind)
    | exact superpose eq536 eq1883
    | exact resolve eq1883 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq1883
  have eq1888 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op X0 x) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1887 X1 X0
       have i₂ := eq16 X0 X1 sF0
       grind)
    | exact superpose eq16 eq1887
    | exact resolve eq1887 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887
  have eq1938 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) X4) = (M.op (M.op (M.op X3 X4) X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 X2 X3 (M.op (M.op X1 (M.op X2 X3)) X0) X4
       have i₂ := eq16 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1942 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) (M.op X3 X1)) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X2 X3) X0) (M.op X3 X1) X2
       have i₂ := eq176 X2 X3 X0 X1
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1951 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op (M.op (M.op X4 X3) X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 (M.op (M.op X3 X1) X4) (M.op (M.op X4 X3) X0)
       have i₂ := eq176 X4 X3 X0 X1
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1990 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X1) X3))) = (M.op (M.op (M.op X0 X1) X4) (M.op X3 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 X4 (M.op (M.op X2 X1) X3) (M.op X3 X2) X0
       have i₂ := eq176 X3 X2 X0 X1
       grind)
    | exact superpose eq176 eq177
    | exact resolve eq177 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2016 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X3 (M.op x y))) = (M.op (M.op (M.op X2 (M.op X3 X0)) X1) (M.op y (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq535 (M.op (M.op X2 (M.op X3 X0)) X1) X3
       have i₂ := eq177 X1 X2 X3 X0
       grind)
    | exact superpose eq177 eq535
    | exact resolve eq535 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2028 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op X3 x)) = (M.op (M.op (M.op X2 (M.op X3 X0)) X1) (M.op y (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1855 eq2016
    | exact resolve eq2016 eq1855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855 eq2016
  have eq2053 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op X3 x)) = (M.op X2 (M.op X1 (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X0)) y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2028 X0 X1 X2 X3
       have i₂ := eq1990 X2 (M.op X3 X0) (M.op X0 (M.op X1 X2)) y X1
       grind)
    | exact superpose eq1990 eq2028
    | exact resolve eq2028 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq2065 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op X3 x)) = (M.op X2 (M.op X1 (M.op (M.op (M.op X2 y) X1) (M.op (M.op X3 X0) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2053 X0 X1 X2 X3
       have i₂ := eq1938 (M.op X3 X0) X0 X1 X2 y
       grind)
    | exact superpose eq1938 eq2053
    | exact resolve eq2053 eq1938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938 eq2053
  have eq2069 : ∀ X0 X2 X3 : G, (M.op (M.op x y) (M.op X3 x)) = (M.op X2 (M.op (M.op (M.op X3 X0) X0) (M.op X2 y))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2065 X0 x X2 X3
       have i₂ := eq16 (M.op (M.op X3 X0) X0) (M.op X2 y) x
       grind)
    | exact superpose eq16 eq2065
    | exact resolve eq2065 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065
  have eq2071 : ∀ X0 X2 X3 : G, (M.op (M.op x y) (M.op X3 x)) = (M.op X2 (M.op X3 (M.op X0 (M.op (M.op y X0) X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2069 X0 X2 X3
       have i₂ := eq1990 X3 X0 y X2 X0
       grind)
    | exact superpose eq1990 eq2069
    | exact resolve eq2069 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990 eq2069
  have eq2073 : ∀ X2 X3 : G, (M.op (M.op x y) (M.op X3 x)) = (M.op X2 (M.op X3 (M.op X2 y))) := by
    intro X2 X3
    first
    | (have i₁ := eq2071 x X2 X3
       have i₂ := eq16 X2 y x
       grind)
    | exact superpose eq16 eq2071
    | exact resolve eq2071 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071
  have eq2177 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op (M.op X1 x) x) X3) X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 (M.op (M.op X1 x) x) X2 X3
       have i₂ := eq1888 X1 X0
       grind)
    | exact superpose eq1888 eq176
    | exact resolve eq176 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2192 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq179 X0 x
       have i₂ := eq1888 X0 (M.op sF0 X0)
       grind)
    | exact superpose eq1888 eq179
    | exact resolve eq179 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2203 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2192 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2192
    | (have j0 := eq2192 X0
       grind)
    | exact resolve eq2192 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192
  have eq2216 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op X3 X1) (M.op (M.op X1 x) x))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq2177 x X1 X2 X3
       have i₂ := eq1951 x X1 X2 X3 (M.op (M.op X1 x) x)
       grind)
    | exact superpose eq1951 eq2177
    | exact resolve eq2177 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951 eq2177
  have eq2225 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op X3 X1) X1)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq2216 X1 X2 X3
       have i₂ := eq1888 X1 (M.op X3 X1)
       grind)
    | exact superpose eq1888 eq2216
    | exact resolve eq2216 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888 eq2216
  have eq2241 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X0 (M.op x y)) X2) (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2203 eq177
    | exact resolve eq177 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2246 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq2203 eq16
    | exact resolve eq16 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2260 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2241 X2 X1 X0
       have i₂ := eq1942 X0 X1 X2 sF0
       grind)
    | exact superpose eq1942 eq2241
    | exact resolve eq2241 eq1942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942 eq2241
  have eq2970 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2225 X1 X3 (M.op X0 (M.op X1 X2))
       have i₂ := eq177 X1 X0 X1 X2
       grind)
    | exact superpose eq177 eq2225
    | exact resolve eq2225 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq3016 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq181 x sF2
       have i₂ := eq2225 sF2 (M.op sF4 x) x
       grind)
    | exact superpose eq2225 eq181
    | exact resolve eq181 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq2225
  have eq3036 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq26 eq3016
    | (have j0 := eq3016 X0
       grind)
    | exact resolve eq3016 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq3119 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X1) (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3036 (M.op (M.op X1 sF4) X0)
       have i₂ := eq16 X0 X1 sF4
       grind)
    | exact superpose eq16 eq3036
    | exact resolve eq3036 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036
  have eq3177 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3119 X0 X1
       have i₂ := eq2260 X0 (M.op X0 X1) (M.op X1 sF4)
       grind)
    | (have i₁ := eq3119 X1 X1
       have i₂ := eq2260 (M.op X1 X1) X1 (M.op X1 sF4)
       grind)
    | exact superpose eq2260 eq3119
    | exact resolve eq3119 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq3185 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 (M.op X0 (M.op X1 (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3177 X1 x
       have i₂ := eq2970 (M.op x sF4) X1 x X1
       grind)
    | (have i₁ := eq3177 X1 X0
       have i₂ := eq2970 X0 X1 (M.op X0 sF4) X1
       grind)
    | exact superpose eq2970 eq3177
    | exact resolve eq3177 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2970 eq3177
  have eq3712 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq976
       grind)
    | exact superpose eq976 eq39
    | exact resolve eq39 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq976
  have eq3713 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3712
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3712
    | exact resolve eq3712 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3712
  have eq3715 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq3713
    | exact resolve eq3713 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713
  have eq3835 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2246 eq2203
    | exact resolve eq2203 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203
  have eq3843 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq3835 X0
       have i₂ := eq2260 X0 (M.op X0 (M.op sF0 sF0)) sF0
       grind)
    | (have i₁ := eq3835 x
       have i₂ := eq2260 (M.op x (M.op sF0 sF0)) x sF0
       grind)
    | exact superpose eq2260 eq3835
    | exact resolve eq3835 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3835
  have eq10733 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (M.op X0 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq554 x X0
       have i₂ := eq2260 X0 sF3 x
       grind)
    | (have i₁ := eq554 x X1
       have i₂ := eq2260 sF3 X1 x
       grind)
    | exact superpose eq2260 eq554
    | exact resolve eq554 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq85409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3715 eq980
    | exact resolve eq980 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980 eq3715
  have eq85417 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq85409
       have r₂ := eq27
       grind)
    | exact resolve eq85409 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85409
  have eq85439 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq85417 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq85417
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq85417
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq85417
       grind)
    | exact resolve eq13 eq85417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85476 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq85439 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85439
  have eq85609 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq85476 eq85417
    | exact resolve eq85417 eq85476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85417 eq85476
  have eq85797 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq85609
  have eq88137 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq85797 eq152
    | exact resolve eq152 eq85797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq85797
  have eq88148 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq88137
    | exact resolve eq88137 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq88137
  have eq88153 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq986 (σ x)
       grind)
    | (have r₁ := eq88148
       have r₂ := eq986 y
       grind)
    | exact resolve eq88148 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88148
  have eq88176 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq88153 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq88153
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq88153
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq88153
       grind)
    | exact resolve eq13 eq88153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88213 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq88176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88176
  have eq88445 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq88213 eq88153
    | exact resolve eq88153 eq88213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88153 eq88213
  have eq88637 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq88445
  have eq88967 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq88637 eq141
    | exact resolve eq141 eq88637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq88637
  have eq88978 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq88967
    | exact resolve eq88967 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq88967
  have eq88983 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq986 y
       grind)
    | (have r₁ := eq88978
       have r₂ := eq986 x
       grind)
    | exact resolve eq88978 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq88978
  have eq88999 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) (M.op X0 x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2073 y X0
       have i₂ := eq88983
       grind)
    | exact superpose eq88983 eq2073
    | exact resolve eq2073 eq88983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073
  have eq89002 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq88983
       grind)
    | exact superpose eq88983 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq88983
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq88983
       grind)
    | exact resolve eq13 eq88983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89039 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq89002 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89002
  have eq89063 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 x)) = (k y (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq89039 eq88999
    | exact resolve eq88999 eq89039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88999
  have eq89750 : ∀ X0 : G, (M.op X0 x) = (k y (M.op (M.op x y) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq89039 (M.op sF0 X0)
       grind)
    | exact superpose eq89039 eq174
    | exact resolve eq174 eq89039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq89752 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq88983
       have i₂ := eq89039 y
       grind)
    | exact superpose eq89039 eq88983
    | exact resolve eq88983 eq89039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88983
  have eq89855 : (M.op x y) = (k y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x y))))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3843 y
       have i₂ := eq89039 (M.op sF0 (M.op y (M.op sF0 sF0)))
       grind)
    | exact superpose eq89039 eq3843
    | exact resolve eq3843 eq89039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843
  have eq89950 : y = (k y y) ∨ x = (M.op x x) := by grind
  clear eq89752
  have eq90031 : (M.op x y) = (k y (M.op x (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89855
       have i₂ := eq535 sF0 sF0
       grind)
    | exact superpose eq535 eq89855
    | exact resolve eq89855 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq89855
  have eq90176 : (M.op x y) = (k y (M.op (M.op x y) (M.op (M.op x y) x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2246 eq90031
    | exact resolve eq90031 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246 eq90031
  have eq90234 : (M.op x y) = (k y (k y (M.op (M.op x y) y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq89063 eq90176
    | exact resolve eq90176 eq89063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89063 eq90176
  have eq90257 : (M.op x y) = (k y (M.op y x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq89750 eq90234
    | exact resolve eq90234 eq89750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89750 eq90234
  have eq90264 : (M.op x y) = (k y (k y x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq89039 eq90257
    | exact resolve eq90257 eq89039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89039 eq90257
  have eq90273 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq993 y X0
       have i₂ := eq89950
       grind)
    | exact superpose eq89950 eq993
    | (have j0 := eq993 y X0
       grind)
    | exact resolve eq993 eq89950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90274 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq991 y
       have i₂ := eq89950
       grind)
    | exact superpose eq89950 eq991
    | (have j0 := eq991 y
       grind)
    | exact resolve eq991 eq89950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991 eq89950
  have eq90281 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq90274
  have eq90282 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq90273 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90273
  have eq90283 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq90281
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq90281
    | exact resolve eq90281 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90281
  have eq90284 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq90282 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq90282
    | (have j0 := eq90282 X0
       grind)
    | exact resolve eq90282 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90282
  have eq90305 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op X0 (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq90283 eq10733
    | exact resolve eq10733 eq90283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10733 eq90283
  have eq90378 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = (k (σ y) (M.op X0 (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq90284 eq90305
    | exact resolve eq90305 eq90284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90305
  have eq91179 : (σ (M.op x y)) = (k (σ y) (k (σ y) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq347 y
       have i₂ := eq90264
       grind)
    | exact superpose eq90264 eq347
    | exact resolve eq347 eq90264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq90264
  have eq91183 : (σ (M.op x y)) = (k (σ y) (k (σ y) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq91179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91179
    | exact resolve eq91179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq91179
  have eq91185 : (σ (M.op x y)) = (k (σ y) (k (σ y) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq91183
    | exact resolve eq91183 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91183
  have eq91377 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ y) (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq90284 eq175
    | exact resolve eq175 eq90284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq91449 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq90284 eq3185
    | exact resolve eq3185 eq90284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185
  have eq91710 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq554 eq91449
    | exact resolve eq91449 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq91449
  have eq91850 : (M.op (σ x) (σ y)) = (k (σ y) (k (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq90378 eq91710
    | exact resolve eq91710 eq90378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90378 eq91710
  have eq91924 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq91377 eq91850
    | exact resolve eq91850 eq91377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91377 eq91850
  have eq91957 : (M.op (σ x) (σ y)) = (k (σ y) (k (σ y) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq90284 eq91924
    | exact resolve eq91924 eq90284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90284 eq91924
  have eq91973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq91185 eq91957
    | exact resolve eq91957 eq91185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91185 eq91957
  have eq91980 : x = (M.op x x) := by
    first
    | (have r₁ := eq91973
       have r₂ := eq27
       grind)
    | exact resolve eq91973 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91973
  have eq92026 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq91980
       grind)
    | exact superpose eq91980 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq91980
       grind)
    | exact resolve eq13 eq91980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92062 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq92026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92026
  have eq92851 : x = (k x x) := by
    first
    | (have i₁ := eq91980
       have i₂ := eq92062 x
       grind)
    | exact superpose eq92062 eq91980
    | exact resolve eq91980 eq92062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91980
  have eq92854 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq92062 y
       grind)
    | exact superpose eq92062 eq18
    | (have j1 := eq92062 y
       grind)
    | exact resolve eq18 eq92062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq92062
  have eq93440 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq993 x X0
       have i₂ := eq92851
       grind)
    | exact superpose eq92851 eq993
    | (have j0 := eq993 x X0
       grind)
    | exact resolve eq993 eq92851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993 eq92851
  have eq93449 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq93440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93440
  have eq93451 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq93449 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq93449
    | (have j0 := eq93449 X0
       grind)
    | exact resolve eq93449 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93449
  have eq93459 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq92854
       grind)
    | exact superpose eq92854 eq40
    | exact resolve eq40 eq92854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq92854
  have eq93461 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq93459
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq93459
    | exact resolve eq93459 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq93459
  have eq93465 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq93461
    | exact resolve eq93461 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq93461
  have eq96811 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq93451 eq26
    | (have j1 := eq93451 (σ y)
       grind)
    | exact resolve eq26 eq93451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq93451
  have eq97161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93465 eq96811
    | exact resolve eq96811 eq93465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93465 eq96811
  have eq97331 : False := by grind
  exact eq97331

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxy_pyx_pxy_Equation3607 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X3) X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op (M.op X1 X3) X0)
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 (M.op X0 X1)) X2) X0) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 (M.op X0 X1)) X2) X0 X1
       have i₂ := eq9 X2 X3 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X2) = (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X0 (M.op X1 (M.op X0 X3))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30 X0 (M.op X1 (M.op X0 X3)) X4 X2
       have i₂ := eq31 X0 X3 X2 X1
       grind)
    | exact superpose eq31 eq30
    | exact resolve eq30 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq209 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X2 X1) X3)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30 X2 X1 X3 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq30 X0 X1 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq209 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq231 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq239 : ∀ X0 X1 X3 : G, (M.op X3 X1) = (M.op X3 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq211 X0 X1 x X3
       have i₂ := eq30 x X1 X3 X1
       grind)
    | exact superpose eq30 eq211
    | (have j0 := eq211 X0 X1 x X3
       grind)
    | exact resolve eq211 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq211
  have eq486 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq231 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq10443 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    grind
  clear eq239
  have eq10453 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq10443 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10443
  have eq10852 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X5) = (M.op (M.op X2 (M.op X5 X1)) (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X4)) ∨ (M.op X3 X4) = (k X3 X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq80 X0 X1 X5 X2 X3
       have i₂ := eq10453 X3 X4 (M.op X0 (M.op X1 (M.op X0 X2)))
       grind)
    | (have i₁ := eq80 X0 X1 X2 X3 X1
       have i₂ := eq10453 X0 X1 (M.op X0 (M.op X1 (M.op X0 X3)))
       grind)
    | exact superpose eq10453 eq80
    | (have j1 := eq10453 X3 X4 X2
       grind)
    | exact resolve eq80 eq10453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10453
  have eq10868 : ∀ X3 X4 X5 : G, (M.op X4 X5) = (M.op X3 X5) ∨ (M.op X3 X4) = (k X3 X4) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq10852 x x x X3 X4 X5
       have i₂ := eq80 x x X5 x X4
       grind)
    | exact superpose eq80 eq10852
    | (have j0 := eq10852 x x x X3 X4 X5
       grind)
    | exact resolve eq10852 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq10852
  have eq11303 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq486 X0 X1
       have j1 := eq10868 X0 X1 x
       grind)
    | (have r₁ := eq486 x x
       have r₂ := eq10868 x x x
       grind)
    | (have r₁ := eq486 x x
       have r₂ := eq10868 x x x
       grind)
    | exact resolve eq486 eq10868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq10868
  have eq11403 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq11303
  have eq11413 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11403 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11403
  have eq11439 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq11413 (σ X0) (σ X1)
       grind)
    | exact superpose eq11413 eq15
    | exact resolve eq15 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11452 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11439 X0 X1
       have i₂ := eq11413 X0 X1
       grind)
    | exact superpose eq11413 eq11439
    | exact resolve eq11439 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11413 eq11439
  have eq11637 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11452 x y
       grind)
    | exact superpose eq11452 eq16
    | (have r₁ := eq16
       have r₂ := eq11452 x y
       grind)
    | exact resolve eq16 eq11452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11452
  have eq11688 : False := by grind
  exact eq11688

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyx_pxy_Equation3607 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq160 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq167 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq160 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq160 X0 X1
       grind)
    | exact superpose eq160 eq13
    | (have j0 := eq13 X1 X1
       have j1 := eq160 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq160 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq160 X0 X0
       grind)
    | exact resolve eq13 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X1
       have i₂ := eq160 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq160 X0 X1
       grind)
    | exact superpose eq160 eq9
    | (have j1 := eq160 X0 X1
       grind)
    | exact resolve eq9 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq194 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq181
    | (have j0 := eq181 X0 X1 X2
       grind)
    | exact resolve eq181 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq198 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq192 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq286 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq378 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq160 X0 X1
       grind)
    | (have i₁ := eq286 X1 X1
       have i₂ := eq160 X0 X1
       grind)
    | exact superpose eq160 eq286
    | (have j0 := eq286 X0 X1
       have j1 := eq160 X0 X1
       grind)
    | (have r₁ := eq286 X1 X1
       have r₂ := eq160 X1 X1
       grind)
    | (have r₁ := eq286 X0 X0
       have r₂ := eq160 X0 X0
       grind)
    | exact resolve eq286 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq399 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq378 X0 X1
       have j1 := eq194 X0 X1 x
       grind)
    | (have r₁ := eq378 X0 X1
       have r₂ := eq194 X0 X1 X1
       grind)
    | (have r₁ := eq378 X1 X0
       have r₂ := eq194 X0 X1 X0
       grind)
    | exact resolve eq378 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq378
  have eq629 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq399 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq637 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq629 X0 X1
       have j1 := eq160 X0 X1
       grind)
    | (have r₁ := eq629 X0 X1
       have r₂ := eq160 X0 X1
       grind)
    | (have r₁ := eq629 X0 X0
       have r₂ := eq160 X0 X0
       grind)
    | exact resolve eq629 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq629
  have eq654 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq637 (σ X0) (σ X1)
       grind)
    | exact superpose eq637 eq15
    | exact resolve eq15 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 X1
       have i₂ := eq637 X0 X1
       grind)
    | exact superpose eq637 eq654
    | exact resolve eq654 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq654
  have eq716 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq661 x y
       grind)
    | exact superpose eq661 eq16
    | (have r₁ := eq16
       have r₂ := eq661 x y
       grind)
    | exact resolve eq16 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq726 : False := by grind
  exact eq726

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_x_pxy_Equation3677 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
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
  have eq50 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
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
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq10
    | exact resolve eq10 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
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
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq71
    | exact resolve eq71 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq70
    | exact resolve eq70 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq87 : (k x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq88 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq87
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq87
    | exact resolve eq87 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
  clear eq44
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq103 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq118 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq122 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq65 sF3
       grind)
    | exact superpose eq65 eq118
    | exact resolve eq118 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq124 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq65 y
       grind)
    | exact superpose eq65 eq122
    | exact resolve eq122 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq155 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq158 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq155
       have i₂ := eq65 sF1
       grind)
    | exact superpose eq65 eq155
    | exact resolve eq155 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq160 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq158
       have i₂ := eq65 sF0
       grind)
    | exact superpose eq65 eq158
    | exact resolve eq158 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq158
  have eq162 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq50 eq160
    | exact resolve eq160 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq163 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq162
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq162
    | exact resolve eq162 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq167 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq163 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq820 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq819 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq819
    | (have j0 := eq819 X0 X1
       grind)
    | exact resolve eq819 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq819
  have eq925 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq820 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq15689 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq167
    | (have j0 := eq167 (σ x)
       grind)
    | exact resolve eq167 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq18326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq18326
    | exact resolve eq18326 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18326
  have eq18342 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq18327
       have r₂ := eq27
       grind)
    | exact resolve eq18327 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18327
  have eq18349 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq18342
    | exact resolve eq18342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18342
  have eq18351 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq163 eq18349
    | exact resolve eq18349 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18349
  have eq18353 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq18351
    | exact resolve eq18351 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18351
  have eq18368 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq18353 eq14
    | exact resolve eq14 eq18353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18353
  have eq18376 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq51 eq18368
    | exact resolve eq18368 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18368
  have eq18378 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq163 eq18376
    | exact resolve eq18376 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18376
  have eq18379 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq18378
  have eq18391 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq18379 eq15689
    | (have r₁ := eq15689
       have r₂ := eq18379
       grind)
    | exact resolve eq15689 eq18379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15689 eq18379
  have eq18401 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq18391
  have eq18563 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq18401 eq104
    | exact resolve eq104 eq18401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq18401
  have eq18578 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq18563
  have eq18607 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq18578 eq88
    | exact resolve eq88 eq18578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq18578
  have eq18638 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq30 eq18607
    | exact resolve eq18607 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18607
  have eq18639 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq18638
  have eq18748 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18639
       grind)
    | exact superpose eq18639 eq124
    | exact resolve eq124 eq18639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18758 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq18639
       grind)
    | exact superpose eq18639 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18639
       grind)
    | exact resolve eq13 eq18639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18639
  have eq18777 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq163 eq18748
    | exact resolve eq18748 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18748
  have eq18780 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq18777
    | exact resolve eq18777 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18777
  have eq31825 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18758 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18758
    | (have j0 := eq18758 x
       grind)
    | (have r₁ := eq18758 x
       have r₂ := eq18
       grind)
    | exact resolve eq18758 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18758
  have eq31831 : (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq31825
  have eq31848 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq925 x y
       have i₂ := eq31831
       grind)
    | exact superpose eq31831 eq925
    | (have j0 := eq925 x y
       grind)
    | exact resolve eq925 eq31831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31831
  have eq31851 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq31848
  have eq31855 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31851
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq31851
    | exact resolve eq31851 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31851
  have eq31873 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31855
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31855
    | exact resolve eq31855 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31855
  have eq31880 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31873
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31873
    | exact resolve eq31873 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31873
  have eq31885 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31880
    | exact resolve eq31880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31880
  have eq31890 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31885
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq31885
    | exact resolve eq31885 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31885
  have eq31895 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq163 eq31890
    | exact resolve eq31890 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31890
  have eq31900 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31895
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31895
    | exact resolve eq31895 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31895
  have eq31905 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31900
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31900
    | exact resolve eq31900 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31900
  have eq31910 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31905
    | exact resolve eq31905 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31905
  have eq32279 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31910 eq14
    | exact resolve eq14 eq31910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31910
  have eq32289 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq51 eq32279
    | exact resolve eq32279 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq32279
  have eq32291 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq163 eq32289
    | exact resolve eq32289 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32289
  have eq32292 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq32291
  have eq32312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq32292 eq18780
    | exact resolve eq18780 eq32292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18780 eq32292
  have eq32364 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq32312
  have eq32375 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq32364
       have r₂ := eq27
       grind)
    | exact resolve eq32364 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32364
  have eq32660 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq32375
       grind)
    | exact superpose eq32375 eq72
    | exact resolve eq72 eq32375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32673 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq32375
       grind)
    | exact superpose eq32375 eq14
    | exact resolve eq14 eq32375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32680 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq50 eq32673
    | exact resolve eq32673 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq32673
  have eq32690 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq32660
    | exact resolve eq32660 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32660
  have eq32699 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124
       have i₂ := eq32680
       grind)
    | exact superpose eq32680 eq124
    | exact resolve eq124 eq32680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32717 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq32680
       grind)
    | exact superpose eq32680 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq32680
       grind)
    | exact resolve eq13 eq32680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32680
  have eq32736 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq163 eq32699
    | exact resolve eq32699 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32699
  have eq32739 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq32736
    | exact resolve eq32736 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32736
  have eq37472 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq32717 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32717
    | (have j0 := eq32717 x
       grind)
    | (have r₁ := eq32717 x
       have r₂ := eq18
       grind)
    | exact resolve eq32717 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq32717
  have eq37478 : (k x y) = (M.op x x) := by grind
  clear eq37472
  have eq37480 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq37478
       have i₂ := eq32375
       grind)
    | exact superpose eq32375 eq37478
    | exact resolve eq37478 eq32375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32375 eq37478
  have eq37856 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq925 x y
       have i₂ := eq37480
       grind)
    | exact superpose eq37480 eq925
    | (have j0 := eq925 x y
       grind)
    | exact resolve eq925 eq37480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq37480
  have eq37860 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq37856
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq37856
    | exact resolve eq37856 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37856
  have eq37874 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq32690 eq37860
    | (have r₁ := eq37860
       have r₂ := eq32690
       grind)
    | exact resolve eq37860 eq32690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37860
  have eq37881 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq37874
       have r₂ := eq20
       grind)
    | exact resolve eq37874 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37874
  have eq37888 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq37881
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq37881
    | exact resolve eq37881 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq37881
  have eq37895 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq32690 eq37888
    | exact resolve eq37888 eq32690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32690 eq37888
  have eq37901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq37895
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37895
    | exact resolve eq37895 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37895
  have eq37905 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq37901
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37901
    | exact resolve eq37901 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37901
  have eq37909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq37905
    | exact resolve eq37905 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37905
  have eq37913 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq37909
       have r₂ := eq27
       grind)
    | exact resolve eq37909 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37909
  have eq37917 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq37913
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq37913
    | exact resolve eq37913 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq37913
  have eq37921 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq163 eq37917
    | exact resolve eq37917 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq37917
  have eq37925 : (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | exact superpose eq32739 eq37921
    | exact resolve eq37921 eq32739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32739 eq37921
  have eq37929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37925
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37925
    | exact resolve eq37925 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37925
  have eq37933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37929
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37929
    | exact resolve eq37929 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37929
  have eq37937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq37933
    | exact resolve eq37933 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37933
  have eq37941 : False := by grind
  exact eq37941

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,X) = m(X,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pyx_y_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq942 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
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
  have eq968 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq942 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq969 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq968 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1002 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq969 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq969 X0 X1
       grind)
    | exact superpose eq969 eq9
    | (have j1 := eq969 X1 X0
       grind)
    | exact resolve eq9 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq1021 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1002 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq1002
    | (have j0 := eq1002 X0 X1
       grind)
    | exact resolve eq1002 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1029 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1021 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1021 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq1021 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq1021 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1055 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1029 (σ X1) (σ X0)
       grind)
    | exact superpose eq1029 eq15
    | exact resolve eq15 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1055 X0 X1
       have i₂ := eq1029 X1 X0
       grind)
    | exact superpose eq1029 eq1055
    | exact resolve eq1055 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029 eq1055
  have eq1601 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1110 x y
       grind)
    | exact superpose eq1110 eq16
    | (have r₁ := eq16
       have r₂ := eq1110 x y
       grind)
    | exact resolve eq16 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1617 : False := by grind
  exact eq1617

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxy_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq268 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq269 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq269 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq271 (σ X0)
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq284
    | exact resolve eq284 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq284
  have eq347 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq347 X0 X1
       have j1 := eq348 X0 X1
       grind)
    | (have r₁ := eq347 X0 X1
       have r₂ := eq348 X0 X1
       grind)
    | exact resolve eq347 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq368 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq349 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq349
    | exact resolve eq349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq349 X0 (σ X1)
       grind)
    | exact superpose eq349 eq15
    | (have j1 := eq349 X0 (σ X1)
       grind)
    | exact resolve eq15 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq398 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq379 X0 X1
       have i₂ := eq303 X1
       grind)
    | exact superpose eq303 eq379
    | (have j0 := eq379 X0 X1
       grind)
    | exact resolve eq379 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq379
  have eq416 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq368 (τ X0) X1
       grind)
    | exact superpose eq368 eq19
    | (have j1 := eq368 (τ X0) X1
       grind)
    | exact resolve eq19 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq368
  have eq553 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq416 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq416
    | exact resolve eq416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq594 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq553
    | (have j0 := eq553 X0 X1
       grind)
    | exact resolve eq553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq852 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq398 x y
       grind)
    | exact superpose eq398 eq16
    | (have j1 := eq398 x y
       grind)
    | exact resolve eq16 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq887 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq852
       have i₂ := eq594 x y
       grind)
    | exact superpose eq594 eq852
    | (have j1 := eq594 x y
       grind)
    | (have r₁ := eq852
       have r₂ := eq594 x y
       grind)
    | exact resolve eq852 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq888 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq887
  have eq896 : x = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq888
       grind)
    | exact superpose eq888 eq9
    | exact resolve eq9 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq901 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq896
       grind)
    | exact resolve eq12 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq903 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq901 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq852
       have i₂ := eq903 y
       grind)
    | exact superpose eq903 eq852
    | exact resolve eq852 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852 eq903
  have eq915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq914
  have eq916 : (σ x) = (σ (M.op y y)) := by grind
  clear eq915
  have eq919 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq916
       grind)
    | exact superpose eq916 eq10
    | exact resolve eq10 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq963 : x = (M.op y y) := by
    first
    | (have i₁ := eq919
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq919
    | exact resolve eq919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq977 : x = (M.op x x) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq963
       grind)
    | exact superpose eq963 eq9
    | exact resolve eq9 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq980 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq348 x X0
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq348
    | (have j0 := eq348 x X0
       grind)
    | exact resolve eq348 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq981 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq977
       grind)
    | exact resolve eq12 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq983 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq981 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq984 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq980 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq1063 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq984 (σ X0)
       grind)
    | exact superpose eq984 eq15
    | exact resolve eq15 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1083 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1063 X0
       have i₂ := eq983 X0
       grind)
    | exact superpose eq983 eq1063
    | exact resolve eq1063 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983 eq1063
  have eq1227 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1083 y
       grind)
    | exact superpose eq1083 eq16
    | (have r₁ := eq16
       have r₂ := eq1083 y
       grind)
    | exact resolve eq16 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1237 : False := by grind
  exact eq1237

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq22
  have eq268 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq269 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq269 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq271 (σ X0)
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq284
    | exact resolve eq284 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq284
  have eq348 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq350 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       have j1 := eq349 X0 X1
       grind)
    | (have r₁ := eq348 X0 X1
       have r₂ := eq349 X0 X1
       grind)
    | exact resolve eq348 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq349
  have eq370 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq350 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq350
    | exact resolve eq350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq350 x (σ y)
       grind)
    | exact superpose eq350 eq16
    | (have j1 := eq350 x (σ y)
       grind)
    | exact resolve eq16 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq381 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq374
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq374
    | exact resolve eq374 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq386 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq370 X1 X0
       grind)
    | exact superpose eq370 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq370 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq370 X0 X1
       grind)
    | exact resolve eq13 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq395 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq393 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq393 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq393 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq410 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq395 X1 (τ X0)
       grind)
    | exact superpose eq395 eq18
    | (have j1 := eq395 X1 (τ X0)
       grind)
    | exact resolve eq18 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq427 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1445 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq410 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq410
    | exact resolve eq410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1473 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq410 X1 (τ X0)
       grind)
    | exact superpose eq410 eq17
    | (have j1 := eq410 X1 (τ X0)
       grind)
    | exact resolve eq17 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq410
  have eq1478 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1473 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1473
    | (have j0 := eq1473 X0 X1
       grind)
    | exact resolve eq1473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1498 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1445 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1445
    | (have j0 := eq1445 X0 X1
       grind)
    | exact resolve eq1445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq1499 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1478 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1478
    | (have j0 := eq1478 X0 X1
       grind)
    | exact resolve eq1478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq1503 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1499 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1499
    | (have j0 := eq1499 X0 X1
       grind)
    | exact resolve eq1499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1576 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1503 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1503
    | exact resolve eq1503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq1641 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1576 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1576
    | (have j0 := eq1576 X0 X1
       grind)
    | exact resolve eq1576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576
  have eq1669 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1641 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1641
    | (have j0 := eq1641 X0 X1
       grind)
    | exact resolve eq1641 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq2059 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq1669 X1 X0
       grind)
    | exact superpose eq1669 eq10
    | (have j1 := eq1669 X1 X0
       grind)
    | exact resolve eq10 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq2108 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2059 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2059
    | (have j0 := eq2059 X0 X1
       grind)
    | exact resolve eq2059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq2180 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2108 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq2108
    | exact resolve eq2108 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2108
  have eq2241 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2180 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2180
    | (have j0 := eq2180 X0 X1
       grind)
    | exact resolve eq2180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq2244 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2241 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2241
    | (have j0 := eq2241 X0 X1
       grind)
    | exact resolve eq2241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241
  have eq2319 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2244 X0 X1
       have i₂ := eq395 X0 X1
       grind)
    | exact superpose eq395 eq2244
    | (have j0 := eq2244 X1 X0
       have j1 := eq395 X1 X0
       grind)
    | exact resolve eq2244 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq2244
  have eq2395 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2319 X0 X1
       have j1 := eq427 X1 X0
       grind)
    | (have r₁ := eq2319 X1 X0
       have r₂ := eq427 X0 X1
       grind)
    | exact resolve eq2319 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2478 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (τ (M.op X1 (σ X0))) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq2395 X1 (σ X0)
       grind)
    | exact superpose eq2395 eq28
    | (have j1 := eq2395 X1 (σ X0)
       grind)
    | exact resolve eq28 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2395
  have eq2494 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (τ (M.op X1 (σ X0))) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2478 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2478
    | (have j0 := eq2478 X0 X1
       grind)
    | exact resolve eq2478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq2522 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2494 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2494
    | (have j0 := eq2494 X0 X1
       grind)
    | exact resolve eq2494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq2962 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2522 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2522
    | exact resolve eq2522 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522
  have eq3042 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ X0)) ∨ (k X0 X1) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2962 X1 X0
       have i₂ := eq370 (σ X1) (σ X0)
       grind)
    | exact superpose eq370 eq2962
    | (have j0 := eq2962 X1 X0
       have j1 := eq370 (σ X1) (σ X0)
       grind)
    | exact resolve eq2962 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962
  have eq3084 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3042 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3042
    | (have j0 := eq3042 X0 X1
       grind)
    | exact resolve eq3042 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042
  have eq3089 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3084 X0 X1
       have j1 := eq427 X0 X1
       grind)
    | (have r₁ := eq3084 X0 X1
       have r₂ := eq427 X0 X1
       grind)
    | exact resolve eq3084 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq3084
  have eq3092 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3089 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3089
    | (have j0 := eq3089 X0 X1
       grind)
    | exact resolve eq3089 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq3126 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3092 y x
       grind)
    | exact superpose eq3092 eq16
    | (have j1 := eq3092 y x
       grind)
    | exact resolve eq16 eq3092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3092
  have eq3196 : y = (k y x) := by
    first
    | (have j1 := eq1498 x y
       grind)
    | (have r₁ := eq3126
       have r₂ := eq1498 x y
       grind)
    | exact resolve eq3126 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498 eq3126
  have eq3809 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq381
       have i₂ := eq370 x y
       grind)
    | exact superpose eq370 eq381
    | (have j1 := eq370 x y
       grind)
    | exact resolve eq381 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3810 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq3809
  have eq3811 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq3810
       have i₂ := eq3196
       grind)
    | exact superpose eq3196 eq3810
    | exact resolve eq3810 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3810
  have eq3812 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3811
       have i₂ := eq3196
       grind)
    | exact superpose eq3196 eq3811
    | exact resolve eq3811 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811
  have eq3813 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq381
       have i₂ := eq3812
       grind)
    | exact superpose eq3812 eq381
    | exact resolve eq381 eq3812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq3812
  have eq3823 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3813
  have eq3824 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3823
       have i₂ := eq3196
       grind)
    | exact superpose eq3196 eq3823
    | exact resolve eq3823 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3823
  have eq3825 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3824
  have eq3827 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3825
       grind)
    | exact superpose eq3825 eq16
    | exact resolve eq16 eq3825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3825
  have eq3852 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq3827
       have i₂ := eq370 x y
       grind)
    | exact superpose eq370 eq3827
    | (have j1 := eq370 x y
       grind)
    | exact resolve eq3827 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq3853 : (M.op x y) = (k y x) := by grind
  clear eq3852
  have eq3855 : y = (M.op x y) := by
    first
    | (have i₁ := eq3853
       have i₂ := eq3196
       grind)
    | exact superpose eq3196 eq3853
    | exact resolve eq3853 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196 eq3853
  have eq3856 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq3827
       have i₂ := eq3855
       grind)
    | exact superpose eq3855 eq3827
    | exact resolve eq3827 eq3855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827 eq3855
  have eq3868 : False := by grind
  exact eq3868

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
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
  have eq79 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq83 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq80 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq80 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq80 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq369 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq378 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq369 X0 X1
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq369 X0 X1
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq369 X0 X0
       have r₂ := eq83 X0 X0
       grind)
    | exact resolve eq369 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq369
  have eq591 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq378 (σ X1) (σ X0)
       grind)
    | exact superpose eq378 eq15
    | exact resolve eq15 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 X1
       have i₂ := eq378 X1 X0
       grind)
    | exact superpose eq378 eq591
    | exact resolve eq591 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq591
  have eq599 : False := by grind
  exact eq599
