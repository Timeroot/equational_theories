import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq174 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq180 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq180
    | (have j0 := eq180 y x
       grind)
    | exact resolve eq180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ y) (σ x)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq180 X0 X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1))) X1
       have r₂ := eq180 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X2
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq195 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq584 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq583 (M.op X0 X0)
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq583
    | exact resolve eq583 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq596 : (σ x) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq584 x
       grind)
    | exact superpose eq584 eq39
    | exact resolve eq39 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq607 : (σ x) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq596
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq596
    | exact resolve eq596 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq645 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq584 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq584
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq584 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq675 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq679 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq191
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq191
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq679
  have eq696 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq702 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq645 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq1110 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq178
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1129 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1132 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1133 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1129 X0 X1
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq1129
    | exact resolve eq1129 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1146 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq696 eq1132
    | (have j0 := eq1132 X0
       have j1 := eq696 X0
       grind)
    | exact resolve eq1132 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq1132
  have eq1162 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1133 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1133
    | (have j0 := eq1133 y x
       grind)
    | exact resolve eq1133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1198 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq190
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq190
    | exact resolve eq190 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq1200 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) y) y
       have r₂ := eq1162
       grind)
    | exact resolve eq13 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1204 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq180 y X0
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq180
    | exact resolve eq180 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq11
    | exact resolve eq11 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1214 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq1211
  have eq1231 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq1198 eq16
    | exact resolve eq16 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1254 : (M.op x y) = (M.op y (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1231
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq1231
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : (M.op x y) = (M.op y (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq1254
  have eq1489 : y = (M.op (M.op x y) (k y y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1214 eq1198
    | exact resolve eq1198 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1499 : y = (M.op (k y y) (k y y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1214 eq1204
    | exact resolve eq1204 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204 eq1214
  have eq1526 : (k y y) = (M.op y (M.op (k y y) (k y y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1489 eq180
    | exact resolve eq180 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1528 : (k y y) = (M.op y y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1499 eq1526
    | exact resolve eq1526 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499 eq1526
  have eq1530 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq1200 y
       grind)
    | (have r₁ := eq1528
       have r₂ := eq1200 y
       grind)
    | exact resolve eq1528 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200 eq1528
  have eq1532 : (k y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq1530
       grind)
    | exact superpose eq1530 eq1162
    | exact resolve eq1162 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1608 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq668
       grind)
    | exact superpose eq668 eq40
    | exact resolve eq40 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq1609 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1608
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1608
    | exact resolve eq1608 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608
  have eq1611 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1609
    | exact resolve eq1609 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609
  have eq1613 : x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1611
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq1611
    | exact resolve eq1611 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq1611
  have eq1615 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1532 eq1613
    | exact resolve eq1613 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532 eq1613
  have eq4035 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq196 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq176 X1 X1 X0 X2
       grind)
    | exact superpose eq176 eq196
    | exact resolve eq196 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4044 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq174 eq196
    | exact resolve eq196 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq4260 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) x) := by
    intro X0
    first
    | exact superpose eq4044 eq196
    | exact resolve eq196 eq4044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq4044
  have eq4417 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1231 eq4260
    | exact resolve eq4260 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq4260
  have eq4448 : (σ x) = (k (σ (M.op (M.op x y) x)) (σ x)) := by
    first
    | (have i₁ := eq607
       have i₂ := eq4417
       grind)
    | exact superpose eq4417 eq607
    | exact resolve eq607 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq4451 : ∀ X0 : G, (M.op (M.op x y) x) ≠ X0 ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq4417
       grind)
    | exact superpose eq4417 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) x) x
       have r₂ := eq4417
       grind)
    | exact resolve eq13 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4453 : x = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq4417
       grind)
    | exact superpose eq4417 eq177
    | exact resolve eq177 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4455 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq180 x X0
       have i₂ := eq4417
       grind)
    | exact superpose eq4417 eq180
    | exact resolve eq180 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4463 : (k x x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq4417
       grind)
    | exact superpose eq4417 eq11
    | exact resolve eq11 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4472 : (k x x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq4463
  have eq5956 : x = (M.op x (k x x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq4472 eq4453
    | exact resolve eq4453 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453
  have eq5962 : x = (M.op (k x x) (k x x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq4472 eq4455
    | exact resolve eq4455 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455 eq4472
  have eq6300 : (k x x) = (M.op x (M.op (k x x) (k x x))) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq180 (k x x) x
       have i₂ := eq5956
       grind)
    | exact superpose eq5956 eq180
    | exact resolve eq180 eq5956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5956
  have eq6309 : (k x x) = (M.op x x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq5962 eq6300
    | exact resolve eq6300 eq5962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5962 eq6300
  have eq6311 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq4451 x
       grind)
    | (have r₁ := eq6309
       have r₂ := eq4451 x
       grind)
    | exact resolve eq6309 eq4451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4451 eq6309
  have eq6315 : (k x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq4417
       have i₂ := eq6311
       grind)
    | exact superpose eq6311 eq4417
    | exact resolve eq4417 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6338 : x = (M.op (k x x) (k x x)) := by
    first
    | (have i₁ := eq180 x x
       have i₂ := eq6311
       grind)
    | exact superpose eq6311 eq180
    | exact resolve eq180 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6311
  have eq13699 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 (M.op X2 (k (M.op X0 X0) X0))) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4035 X0 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq4035
    | exact resolve eq4035 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq13794 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq4035 X1 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4035
    | (have j0 := eq4035 X1 x y X0
       grind)
    | exact resolve eq4035 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13896 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4035 (M.op X0 X1) X0 X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq16 (M.op X0 X1) x x
       grind)
    | exact superpose eq16 eq4035
    | exact resolve eq4035 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14029 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq13794 X0 X1
       have i₂ := eq4417
       grind)
    | exact superpose eq4417 eq13794
    | exact resolve eq13794 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4417 eq13794
  have eq14063 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13699 X0 X1 X2
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq13699
    | exact resolve eq13699 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq13699
  have eq14078 : ∀ X0 X1 : G, (k x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | exact superpose eq6315 eq14029
    | exact resolve eq14029 eq6315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14029
  have eq14101 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13896 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq180 X0 X1
       grind)
    | exact superpose eq180 eq13896
    | exact resolve eq13896 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14850 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) (M.op (k X0 X0) (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14063 (k X0 X0) X1 (M.op x (M.op X0 x))
       have i₂ := eq702 X0 x x
       grind)
    | exact superpose eq702 eq14063
    | (have j1 := eq702 X0 X1 x
       grind)
    | exact resolve eq14063 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq14920 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1262 eq14063
    | exact resolve eq14063 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq14946 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq687 eq14063
    | exact resolve eq14063 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq15079 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4035 X4 (M.op X1 (M.op X2 X0)) (M.op X0 X0) X3
       have i₂ := eq14063 X0 X1 X2
       grind)
    | exact superpose eq14063 eq4035
    | exact resolve eq4035 eq14063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035
  have eq15081 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13896 (M.op X1 (M.op X2 X0)) (M.op X0 X0)
       have i₂ := eq14063 X0 X1 X2
       grind)
    | exact superpose eq14063 eq13896
    | exact resolve eq13896 eq14063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15083 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15081 X0 X1 X2
       have i₂ := eq14101 (M.op X2 X0) X1
       grind)
    | exact superpose eq14101 eq15081
    | exact resolve eq15081 eq14101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15081
  have eq15084 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq15079 X0 X1 X2 X3 X4
       have i₂ := eq14101 (M.op X2 X0) X1
       grind)
    | exact superpose eq14101 eq15079
    | exact resolve eq15079 eq14101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15079
  have eq15114 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1146 eq14946
    | (have j1 := eq1146 (σ y)
       grind)
    | exact resolve eq14946 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14946
  have eq15131 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1146 eq14920
    | (have j1 := eq1146 (M.op x y)
       grind)
    | exact resolve eq14920 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14920
  have eq15170 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1146 eq14850
    | (have j0 := eq14850 X0 X1
       have j1 := eq1146 X0
       grind)
    | exact resolve eq14850 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146 eq14850
  have eq15174 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq15084 X0 X1 X2 X3 X4
       have i₂ := eq15083 X0 X1 X2
       grind)
    | exact superpose eq15083 eq15084
    | exact resolve eq15084 eq15083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15083 eq15084
  have eq15181 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15114 x
       have i₂ := eq1133 sF3 x
       grind)
    | exact superpose eq1133 eq15114
    | exact resolve eq15114 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15114
  have eq15190 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq15131 x
       have i₂ := eq1133 sF0 x
       grind)
    | exact superpose eq1133 eq15131
    | exact resolve eq15131 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15131
  have eq15210 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15170 X0 x
       have i₂ := eq1133 X0 x
       grind)
    | exact superpose eq1133 eq15170
    | (have j0 := eq15170 X0 x
       grind)
    | exact resolve eq15170 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133 eq15170
  have eq15213 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq15181
       have r₂ := eq13 (k (σ y) (σ y)) (σ y)
       grind)
    | (have r₁ := eq15181
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq15181 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15181
  have eq15214 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq15190
       have r₂ := eq13 (k (M.op x y) (M.op x y)) (M.op x y)
       grind)
    | (have r₁ := eq15190
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq15190 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15190
  have eq15216 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15210 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq15210 x
       have r₂ := eq13 (k x x) x
       grind)
    | (have r₁ := eq15210 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq15210 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq15210 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15210
  have eq15218 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) := by
    first
    | exact superpose eq15213 eq191
    | exact resolve eq191 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq15305 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq15216 X0
       grind)
    | exact superpose eq15216 eq177
    | exact resolve eq177 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq15328 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13896 X0 X0
       have i₂ := eq15216 X0
       grind)
    | exact superpose eq15216 eq13896
    | exact resolve eq13896 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13896
  have eq15330 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X1) X1
       have i₂ := eq15216 (M.op X0 X1)
       grind)
    | exact superpose eq15216 eq16
    | exact resolve eq16 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15405 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq180 X0 X0
       have i₂ := eq15216 (M.op X0 X0)
       grind)
    | exact superpose eq15216 eq180
    | exact resolve eq180 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15422 : x = (k (k x x) (k x x)) := by
    first
    | (have i₁ := eq6338
       have i₂ := eq15216 (k x x)
       grind)
    | exact superpose eq15216 eq6338
    | exact resolve eq6338 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6338
  have eq15517 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq15405 X0
       have i₂ := eq15216 X0
       grind)
    | exact superpose eq15216 eq15405
    | exact resolve eq15405 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15405
  have eq15571 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15330 X0 X1
       have i₂ := eq15216 X0
       grind)
    | exact superpose eq15216 eq15330
    | exact resolve eq15330 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15330
  have eq15838 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) (M.op (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14063 (k X0 X0) X1 X0
       have i₂ := eq15305 X0
       grind)
    | exact superpose eq15305 eq14063
    | exact resolve eq14063 eq15305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14063
  have eq15848 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15838 X0 X1
       have i₂ := eq15216 (k X0 X0)
       grind)
    | exact superpose eq15216 eq15838
    | exact resolve eq15838 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15838
  have eq15853 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15848 X0 X1
       have i₂ := eq15517 X0
       grind)
    | exact superpose eq15517 eq15848
    | exact resolve eq15848 eq15517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15848
  have eq16905 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15328 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq15328
    | exact resolve eq15328 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19680 : ∀ X0 : G, (k x x) = (M.op (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) x) := by
    intro X0
    first
    | (have i₁ := eq14078 (k (M.op x sF0) (M.op x sF0)) x
       have i₂ := eq15328 (M.op x sF0)
       grind)
    | exact superpose eq15328 eq14078
    | exact resolve eq14078 eq15328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14078
  have eq26130 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15216 (M.op X1 X0)
       have i₂ := eq14101 X0 X1
       grind)
    | exact superpose eq14101 eq15216
    | exact resolve eq15216 eq14101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26136 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq180 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq14101 X0 X1
       grind)
    | exact superpose eq14101 eq180
    | exact resolve eq180 eq14101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq14101
  have eq26158 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26136 X0 X1
       have i₂ := eq15174 X0 X0 X1 X0 X1
       grind)
    | exact superpose eq15174 eq26136
    | exact resolve eq26136 eq15174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26136
  have eq39116 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (M.op (k (k x x) (k x x)) (k (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq19680 eq15571
    | exact resolve eq15571 eq19680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15571 eq19680
  have eq39126 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (M.op (k (k x x) (k x x)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39116 X0
       have i₂ := eq15517 (M.op X0 sF0)
       grind)
    | exact superpose eq15517 eq39116
    | exact resolve eq39116 eq15517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39116
  have eq39170 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39126 X0
       have i₂ := eq15422
       grind)
    | exact superpose eq15422 eq39126
    | exact resolve eq39126 eq15422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15422 eq39126
  have eq39185 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39170 x
       have i₂ := eq26130 sF0 x
       grind)
    | exact superpose eq26130 eq39170
    | exact resolve eq39170 eq26130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39170
  have eq70083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1615 eq675
    | exact resolve eq675 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq70094 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq70083
       have r₂ := eq27
       grind)
    | exact resolve eq70083 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70083
  have eq70102 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15213 eq70094
    | exact resolve eq70094 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70094
  have eq70497 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq70102 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq70102
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq70102
       grind)
    | exact resolve eq12 eq70102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70531 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by grind
  clear eq70497
  have eq70548 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15213 eq70531
    | exact resolve eq70531 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70531
  have eq70549 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by grind
  clear eq70548
  have eq70560 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1615 eq70549
    | exact resolve eq70549 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615 eq70549
  have eq70569 : (τ (σ x)) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq70560 eq115
    | exact resolve eq115 eq70560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq70560
  have eq70664 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq70569
    | exact resolve eq70569 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70569
  have eq70665 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by grind
  clear eq70664
  have eq70726 : (k x x) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq15853 x y
       have i₂ := eq70665
       grind)
    | exact superpose eq70665 eq15853
    | exact resolve eq15853 eq70665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15853
  have eq70743 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | exact superpose eq70665 eq70726
    | exact resolve eq70726 eq70665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70665 eq70726
  have eq71190 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq15517 x
       have i₂ := eq70743
       grind)
    | exact superpose eq70743 eq15517
    | exact resolve eq15517 eq70743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70743
  have eq71207 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq71190
  have eq71268 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq71207
       grind)
    | exact superpose eq71207 eq40
    | exact resolve eq40 eq71207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71279 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15305 y
       have i₂ := eq71207
       grind)
    | exact superpose eq71207 eq15305
    | exact resolve eq15305 eq71207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15305
  have eq71287 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15328 y
       have i₂ := eq71207
       grind)
    | exact superpose eq71207 eq15328
    | exact resolve eq15328 eq71207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15328
  have eq71296 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16905 y
       have i₂ := eq71207
       grind)
    | exact superpose eq71207 eq16905
    | exact resolve eq16905 eq71207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71207
  have eq71310 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq71296
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq71296
    | exact resolve eq71296 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71296
  have eq71315 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71287
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq71287
    | exact resolve eq71287 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71287
  have eq71320 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq71268
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq71268
    | exact resolve eq71268 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71268
  have eq71345 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq71310
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq71310
    | exact resolve eq71310 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71310
  have eq71351 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq71320
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq71320
    | exact resolve eq71320 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71320
  have eq71358 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq71345
    | exact resolve eq71345 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71345
  have eq71512 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq71358 eq27
    | exact resolve eq27 eq71358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71358
  have eq72068 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26130 x y
       have i₂ := eq71279
       grind)
    | exact superpose eq71279 eq26130
    | exact resolve eq26130 eq71279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26130 eq71279
  have eq72082 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq72068
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq72068
    | exact resolve eq72068 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72068
  have eq72668 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq72082
       grind)
    | exact superpose eq72082 eq40
    | exact resolve eq40 eq72082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq72082
  have eq72727 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq72668
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq72668
    | exact resolve eq72668 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq72668
  have eq72766 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq72727
    | exact resolve eq72727 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72727
  have eq72780 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq71351 eq72766
    | exact resolve eq72766 eq71351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71351 eq72766
  have eq72784 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq72780
       have r₂ := eq71512
       grind)
    | exact resolve eq72780 eq71512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71512 eq72780
  have eq72786 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq72784 eq28
    | exact resolve eq28 eq72784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq72808 : (k (M.op x y) (M.op x y)) = (τ (k (σ y) (σ y))) := by
    first
    | exact superpose eq72784 eq133
    | exact resolve eq133 eq72784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq72858 : (k (M.op x y) (M.op x y)) = (k y (τ (σ y))) := by
    first
    | exact superpose eq107 eq72808
    | exact resolve eq72808 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq72808
  have eq72893 : (k y y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31 eq72858
    | exact resolve eq72858 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72858
  have eq72939 : y = (M.op x y) := by
    first
    | exact superpose eq72786 eq31
    | exact resolve eq31 eq72786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq72940 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq72786 eq14
    | exact resolve eq14 eq72786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73030 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq72939
       grind)
    | exact superpose eq72939 eq18
    | exact resolve eq18 eq72939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq74159 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq73030 eq39185
    | exact resolve eq39185 eq73030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39185
  have eq74208 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq73030 eq74159
    | exact resolve eq74159 eq73030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73030 eq74159
  have eq74219 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq74208
       have i₂ := eq15216 sF0
       grind)
    | exact superpose eq15216 eq74208
    | exact resolve eq74208 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74208
  have eq74253 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq74219 eq37
    | exact resolve eq37 eq74219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq74321 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq74253
    | exact resolve eq74253 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74253
  have eq74351 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq72784 eq74321
    | exact resolve eq74321 eq72784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74321
  have eq74404 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq74351 eq15218
    | exact resolve eq15218 eq74351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15218
  have eq74596 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ y) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq74404 eq176
    | exact resolve eq176 eq74404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq74404
  have eq74630 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ y) (M.op X1 (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq74596 X1 X0
       have i₂ := eq15174 X0 X1 sF3 X1 sF3
       grind)
    | exact superpose eq15174 eq74596
    | exact resolve eq74596 eq15174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15174 eq74596
  have eq146113 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq74630 X0 X0
       have i₂ := eq26158 X0 sF3
       grind)
    | exact superpose eq26158 eq74630
    | exact resolve eq74630 eq26158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26158 eq74630
  have eq146465 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq70102 eq146113
    | exact resolve eq146113 eq70102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70102 eq146113
  have eq146831 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15213 eq146465
    | exact resolve eq146465 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15213 eq146465
  have eq146881 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq74351 eq146831
    | exact resolve eq146831 eq74351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146831
  have eq146905 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq146881
    | exact resolve eq146881 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146881
  have eq146917 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq74351 eq146905
    | exact resolve eq146905 eq74351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146905
  have eq146921 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq146917
       have i₂ := eq72893
       grind)
    | exact superpose eq72893 eq146917
    | exact resolve eq146917 eq72893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72893 eq146917
  have eq146924 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq74219 eq146921
    | exact resolve eq146921 eq74219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146921
  have eq146925 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq146924
       have i₂ := eq72939
       grind)
    | exact superpose eq72939 eq146924
    | exact resolve eq146924 eq72939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72939 eq146924
  have eq146926 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6315 eq146925
    | exact resolve eq146925 eq6315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6315 eq146925
  have eq179479 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15517 x
       have i₂ := eq146926
       grind)
    | exact superpose eq146926 eq15517
    | exact resolve eq15517 eq146926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15517 eq146926
  have eq179520 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74219 eq179479
    | exact resolve eq179479 eq74219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74219 eq179479
  have eq179521 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq179520
  have eq179587 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179521 eq27
    | exact resolve eq27 eq179521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179521
  have eq179873 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq179587
       have r₂ := eq71315
       grind)
    | exact resolve eq179587 eq71315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71315 eq179587
  have eq180108 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179873 eq72786
    | exact resolve eq72786 eq179873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72786 eq179873
  have eq180217 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq180108
    | exact resolve eq180108 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq180108
  have eq180218 : x = (M.op x y) := by grind
  clear eq180217
  have eq180358 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq180218
       grind)
    | exact superpose eq180218 eq22
    | exact resolve eq22 eq180218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq180397 : (σ x) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq4448
       have i₂ := eq180218
       grind)
    | exact superpose eq180218 eq4448
    | exact resolve eq4448 eq180218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4448 eq180218
  have eq180583 : (σ x) = (k (σ (k (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq15214 eq180397
    | exact resolve eq180397 eq15214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15214 eq180397
  have eq180616 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq41 eq180583
    | exact resolve eq180583 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180583
  have eq180641 : (σ x) = (k (k (σ (M.op x y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq72784 eq180616
    | exact resolve eq180616 eq72784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180616
  have eq180660 : (σ x) = (k (k (σ (M.op x y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq20 eq180641
    | exact resolve eq180641 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180641
  have eq180674 : (σ x) = (k (k (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq72784 eq180660
    | exact resolve eq180660 eq72784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180660
  have eq180680 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq74351 eq180674
    | exact resolve eq180674 eq74351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74351 eq180674
  have eq180690 : (σ x) = (σ y) := by
    first
    | exact superpose eq180358 eq72940
    | exact resolve eq72940 eq180358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72940
  have eq180691 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq180358 eq20
    | exact resolve eq20 eq180358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180774 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (k (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq180358 eq16905
    | exact resolve eq16905 eq180358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16905 eq180358
  have eq180797 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq41 eq180774
    | exact resolve eq180774 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq180774
  have eq180884 : (k (σ (M.op x y)) (σ y)) = (M.op (k (σ (M.op x y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq72784 eq180797
    | exact resolve eq180797 eq72784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180797
  have eq180967 : (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq180690 eq180884
    | exact resolve eq180884 eq180690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180884
  have eq181040 : (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq20 eq180967
    | exact resolve eq180967 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq180967
  have eq181084 : (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq72784 eq181040
    | exact resolve eq181040 eq72784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72784 eq181040
  have eq181109 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq180680 eq181084
    | exact resolve eq181084 eq180680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180680 eq181084
  have eq181121 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq181109
       have i₂ := eq15216 sF2
       grind)
    | exact superpose eq15216 eq181109
    | exact resolve eq181109 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181109
  have eq181129 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq180690 eq26
    | exact resolve eq26 eq180690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq180690
  have eq181538 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq181129
       have i₂ := eq15216 sF2
       grind)
    | exact superpose eq15216 eq181129
    | exact resolve eq181129 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15216 eq181129
  have eq181614 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq181121 eq181538
    | exact resolve eq181538 eq181121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181121 eq181538
  have eq181918 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq181614 eq27
    | exact resolve eq27 eq181614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq181614
  have eq182269 : False := by grind
  exact eq182269

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq69 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq14 (τ X1) (τ X0)
       grind)
    | exact superpose eq14 eq35
    | (have j1 := eq14 (τ X1) (τ X0)
       grind)
    | exact resolve eq35 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq263 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq25 (M.op X0 X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq25
    | exact resolve eq25 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq62 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq376 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq380 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq376 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq376
    | (have j0 := eq376 X0
       grind)
    | exact resolve eq376 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq555 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X0 X1
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq82
    | exact resolve eq82 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq82
  have eq2231 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq34
    | (have j1 := eq380 X0
       grind)
    | exact resolve eq34 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq380
  have eq2259 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2231 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2231
    | (have j0 := eq2231 X0
       grind)
    | exact resolve eq2231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2260 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2265 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2260 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2260
    | exact resolve eq2260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2276 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq2260 X0
       grind)
    | exact superpose eq2260 eq10
    | exact resolve eq10 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2316 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2265 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2265
    | exact resolve eq2265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265
  have eq2390 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq2316 X0
       grind)
    | exact superpose eq2316 eq10
    | exact resolve eq10 eq2316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2443 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2390 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2390
    | exact resolve eq2390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390
  have eq2539 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2443 (σ X0)
       grind)
    | exact superpose eq2443 eq15
    | exact resolve eq15 eq2443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2561 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2539 X0
       have i₂ := eq2316 X0
       grind)
    | exact superpose eq2316 eq2539
    | exact resolve eq2539 eq2316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316 eq2539
  have eq3084 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2276 X0
       have i₂ := eq2443 X0
       grind)
    | exact superpose eq2443 eq2276
    | exact resolve eq2276 eq2443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276 eq2443
  have eq3317 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (τ X0)
       have i₂ := eq3084 X0
       grind)
    | exact superpose eq3084 eq25
    | exact resolve eq25 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq3593 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq263 (σ X0)
       have i₂ := eq2561 X0
       grind)
    | exact superpose eq2561 eq263
    | exact resolve eq263 eq2561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522747 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq3084 X0
       grind)
    | exact superpose eq3084 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3084
  have eq523095 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3317 X1
       have i₂ := eq522747 X1 X0
       grind)
    | (have i₁ := eq3317 X0
       have i₂ := eq522747 X0 (M.op X0 X0)
       grind)
    | exact superpose eq522747 eq3317
    | (have j1 := eq522747 X1 X0
       grind)
    | exact resolve eq3317 eq522747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317 eq522747
  have eq523315 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq523095 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523095
  have eq571179 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq523315 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq523315
    | exact resolve eq523315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523315
  have eq572109 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq571179 X0 X1
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq571179
    | (have j0 := eq571179 X0 X1
       grind)
    | exact resolve eq571179 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq571179
  have eq573022 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq572109 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq572109
    | exact resolve eq572109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573061 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq572109 X0 X1
       grind)
    | exact superpose eq572109 eq18
    | (have j1 := eq572109 X0 X1
       grind)
    | exact resolve eq18 eq572109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq572109
  have eq577552 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq573022 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq573022
    | (have j0 := eq573022 (σ X0) (σ X1)
       grind)
    | exact resolve eq573022 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573022
  have eq583490 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq573061 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq573061
    | exact resolve eq573061 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573061
  have eq584146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq583490 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq583490
    | (have j0 := eq583490 X0 X1
       grind)
    | exact resolve eq583490 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583490
  have eq992932 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq577552 y x
       grind)
    | exact superpose eq577552 eq16
    | (have j1 := eq577552 y x
       grind)
    | exact resolve eq16 eq577552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577552
  have eq994630 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq992932
       have i₂ := eq584146 y x
       grind)
    | exact superpose eq584146 eq992932
    | (have j1 := eq584146 (σ y) (σ x)
       grind)
    | (have r₁ := eq992932
       have r₂ := eq584146 y x
       grind)
    | exact resolve eq992932 eq584146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584146 eq992932
  have eq994631 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq994630
  have eq994660 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq555 y x
       have i₂ := eq994631
       grind)
    | exact superpose eq994631 eq555
    | exact resolve eq555 eq994631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998850 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq994660
       grind)
    | exact superpose eq994660 eq16
    | exact resolve eq16 eq994660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994660
  have eq1001080 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq998850
       have i₂ := eq994631
       grind)
    | exact superpose eq994631 eq998850
    | exact resolve eq998850 eq994631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994631 eq998850
  have eq1001083 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq1001080
  have eq1001151 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq555 (σ y) (σ x)
       have i₂ := eq1001083
       grind)
    | exact superpose eq1001083 eq555
    | exact resolve eq555 eq1001083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq1001716 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1001151
       have i₂ := eq2561 y
       grind)
    | exact superpose eq2561 eq1001151
    | exact resolve eq1001151 eq2561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561 eq1001151
  have eq1025234 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1001083
       have i₂ := eq1001716
       grind)
    | exact superpose eq1001716 eq1001083
    | exact resolve eq1001083 eq1001716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001083 eq1001716
  have eq1025750 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1025234
  have eq1028283 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1025750
       grind)
    | exact superpose eq1025750 eq10
    | exact resolve eq10 eq1025750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025750
  have eq1028770 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1028283
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1028283
    | exact resolve eq1028283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028283
  have eq1028771 : x = (M.op y y) := by grind
  clear eq1028770
  have eq1029003 : x = (M.op x y) := by
    first
    | (have i₁ := eq263 y
       have i₂ := eq1028771
       grind)
    | exact superpose eq1028771 eq263
    | exact resolve eq263 eq1028771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq1029016 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3593 y
       have i₂ := eq1028771
       grind)
    | exact superpose eq1028771 eq3593
    | exact resolve eq3593 eq1028771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593 eq1028771
  have eq1070935 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1029016
       grind)
    | exact superpose eq1029016 eq16
    | exact resolve eq16 eq1029016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029016
  have eq1071642 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1070935
       have i₂ := eq1029003
       grind)
    | exact superpose eq1029003 eq1070935
    | exact resolve eq1070935 eq1029003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029003 eq1070935
  have eq1071643 : False := by grind
  exact eq1071643

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq57 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  clear eq18
  have eq140 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56 x y
       grind)
    | exact superpose eq56 eq16
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq16 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq23
    | (have j1 := eq56 X0 X0
       grind)
    | exact resolve eq23 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq159 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq250 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq20 X1 X1 X0 X2
       grind)
    | exact superpose eq20 eq31
    | exact resolve eq31 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31
  have eq354 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq250 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq21 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq250
    | exact resolve eq250 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq1304 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57
    | exact resolve eq57 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1352 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1304 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1304
    | (have j0 := eq1304 X0 X1
       grind)
    | exact resolve eq1304 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq3322 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq140
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq140
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq140 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq3323 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq3322
  have eq17736 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 (σ (τ X0))) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq159 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq159
    | (have j0 := eq159 (τ X0) X1
       grind)
    | exact resolve eq159 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq17865 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17736 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17736
    | (have j0 := eq17736 X0 X1
       grind)
    | exact resolve eq17736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17736
  have eq17890 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17865 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17865
    | (have j0 := eq17865 X0 X1
       grind)
    | exact resolve eq17865 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17865
  have eq17969 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq354 (k X0 X0) X0
       have i₂ := eq17890 X0 (k X0 X0)
       grind)
    | exact superpose eq17890 eq354
    | (have j1 := eq17890 X0 x
       grind)
    | exact resolve eq354 eq17890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq17890
  have eq18211 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k X0 X0) (k X0 X0)
       have i₂ := eq17969 X0
       grind)
    | exact superpose eq17969 eq23
    | (have j1 := eq17969 X0
       grind)
    | exact resolve eq23 eq17969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17969
  have eq18551 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq18211 (σ X0)
       grind)
    | exact superpose eq18211 eq15
    | (have j1 := eq18211 (σ X0)
       grind)
    | exact resolve eq15 eq18211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18211
  have eq56900 : x ≠ x ∨ x = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3323
       grind)
    | exact superpose eq3323 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3323
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3323
       grind)
    | exact resolve eq13 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323
  have eq57015 : x ≠ x ∨ x = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56900
  have eq57016 : x = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq57015
  have eq113127 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq18551
  have eq113404 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113127 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq113127
    | (have j0 := eq113127 X0
       grind)
    | exact resolve eq113127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113127
  have eq113405 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq113404 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113404
  have eq113902 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq113405 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq113405
    | exact resolve eq113405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113991 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq113405 X0
       grind)
    | exact superpose eq113405 eq21
    | exact resolve eq21 eq113405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114357 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq113902 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq113902
    | exact resolve eq113902 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq113902
  have eq114421 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq114357 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq114357
    | exact resolve eq114357 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114357
  have eq119150 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq113991 X0
       have i₂ := eq114421 X0
       grind)
    | exact superpose eq114421 eq113991
    | exact resolve eq113991 eq114421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113991
  have eq3098445 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq153 x y
       have i₂ := eq57016
       grind)
    | exact superpose eq57016 eq153
    | (have j0 := eq153 x y
       grind)
    | exact resolve eq153 eq57016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq57016
  have eq3098503 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3098445
  have eq3098504 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3098503
  have eq3098514 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3098504
       have i₂ := eq113405 x
       grind)
    | exact superpose eq113405 eq3098504
    | exact resolve eq3098504 eq113405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098504
  have eq3098520 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3098514
       have i₂ := eq114421 x
       grind)
    | exact superpose eq114421 eq3098514
    | exact resolve eq3098514 eq114421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098514
  have eq3098534 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3098520
       grind)
    | exact superpose eq3098520 eq16
    | exact resolve eq16 eq3098520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3098630 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3098520
       grind)
    | exact superpose eq3098520 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3098520
       grind)
    | exact resolve eq13 eq3098520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098520
  have eq3099144 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq3098630
  have eq3099399 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3099144
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3099144
    | exact resolve eq3099144 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099144
  have eq3099622 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3099399
       have i₂ := eq113405 x
       grind)
    | exact superpose eq113405 eq3099399
    | exact resolve eq3099399 eq113405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113405 eq3099399
  have eq3099740 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3099622
       have i₂ := eq114421 x
       grind)
    | exact superpose eq114421 eq3099622
    | exact resolve eq3099622 eq114421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114421 eq3099622
  have eq3099741 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq3099740
  have eq3105010 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1352 y x
       have i₂ := eq3099741
       grind)
    | exact superpose eq3099741 eq1352
    | (have j0 := eq1352 y x
       grind)
    | exact resolve eq1352 eq3099741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352 eq3099741
  have eq3105679 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq3105010
  have eq3106099 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq3105679
       have r₂ := eq3098534
       grind)
    | exact resolve eq3105679 eq3098534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105679
  have eq3110891 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3098534
       have i₂ := eq3106099
       grind)
    | exact superpose eq3106099 eq3098534
    | exact resolve eq3098534 eq3106099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098534 eq3106099
  have eq3111407 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq3110891
  have eq3111408 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq3111407
  have eq3111743 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq3111408
       grind)
    | exact superpose eq3111408 eq10
    | exact resolve eq10 eq3111408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111408
  have eq3112898 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3111743
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3111743
    | exact resolve eq3111743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111743
  have eq3112899 : y = (M.op x x) := by grind
  clear eq3112898
  have eq3118079 : x = (M.op x y) := by
    first
    | (have i₁ := eq21 x
       have i₂ := eq3112899
       grind)
    | exact superpose eq3112899 eq21
    | exact resolve eq21 eq3112899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3118247 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq119150 x
       have i₂ := eq3112899
       grind)
    | exact superpose eq3112899 eq119150
    | exact resolve eq119150 eq3112899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119150 eq3112899
  have eq3147738 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3118247
       grind)
    | exact superpose eq3118247 eq16
    | exact resolve eq16 eq3118247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118247
  have eq3148761 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3147738
       have i₂ := eq3118079
       grind)
    | exact superpose eq3118079 eq3147738
    | exact resolve eq3147738 eq3118079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118079 eq3147738
  have eq3148762 : False := by grind
  exact eq3148762

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq65 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  clear eq45
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq64
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq65
    | exact resolve eq65 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq68
    | exact resolve eq68 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq56
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq75
  have eq244 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y) (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq566 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq50
    | (have j1 := eq61 X0 X0
       grind)
    | exact resolve eq50 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq580 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq584 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq572
    | (have j0 := eq572 X0 X1
       grind)
    | exact resolve eq572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq3404 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq425
    | exact resolve eq425 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq3433 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3404
    | (have j0 := eq3404 (σ y) (σ x)
       grind)
    | exact resolve eq3404 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3757 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq580 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq580
    | (have j0 := eq580 (τ X0)
       grind)
    | exact resolve eq580 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq580
  have eq3778 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3757 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3757
    | (have j0 := eq3757 X0
       grind)
    | exact resolve eq3757 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3757
  have eq3790 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3778 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3778
    | (have j0 := eq3778 X0
       grind)
    | exact resolve eq3778 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778
  have eq4035 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq428 X0 X0 X2 X3 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq428
    | exact resolve eq428 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq20634 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4035 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq4035
    | exact resolve eq4035 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq4035
  have eq26287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq69 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq26288 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq26287
    | exact resolve eq26287 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26287
  have eq26299 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26288
       have r₂ := eq28
       grind)
    | exact resolve eq26288 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26288
  have eq26331 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26299 eq3404
    | exact resolve eq3404 eq26299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27951 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26331 eq26299
    | exact resolve eq26299 eq26331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26299 eq26331
  have eq27991 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq27951
  have eq28020 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27991 eq52
    | exact resolve eq52 eq27991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27991
  have eq28039 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq28020
  have eq28100 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28039 eq20634
    | exact resolve eq20634 eq28039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28039
  have eq28104 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28100
    | exact resolve eq28100 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28100
  have eq28148 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3404 x y
       have i₂ := eq28104
       grind)
    | exact superpose eq28104 eq3404
    | exact resolve eq3404 eq28104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404
  have eq29836 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28104
       have i₂ := eq28148
       grind)
    | exact superpose eq28148 eq28104
    | exact resolve eq28104 eq28148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28104 eq28148
  have eq29878 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq29836
  have eq29909 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq29878
       grind)
    | exact superpose eq29878 eq52
    | exact resolve eq52 eq29878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29878
  have eq29930 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29909
  have eq29961 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq29974 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq29930
       grind)
    | exact superpose eq29930 eq52
    | exact resolve eq52 eq29930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq29993 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20634 y y
       have i₂ := eq29930
       grind)
    | exact superpose eq29930 eq20634
    | exact resolve eq20634 eq29930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20634 eq29930
  have eq29997 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29993
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29993
    | exact resolve eq29993 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29993
  have eq30013 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29997 eq244
    | exact resolve eq244 eq29997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq30021 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29997 eq3433
    | exact resolve eq3433 eq29997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3433
  have eq30074 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq30021
    | exact resolve eq30021 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30021
  have eq30212 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq29974
       grind)
    | exact superpose eq29974 eq67
    | exact resolve eq67 eq29974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq29974
  have eq30261 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30212
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30212
    | exact resolve eq30212 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30212
  have eq32227 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30074 eq30013
    | exact resolve eq30013 eq30074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30013 eq30074
  have eq32273 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq32227
  have eq32281 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29997 eq32273
    | exact resolve eq32273 eq29997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29997 eq32273
  have eq32318 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32281
  have eq32396 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32318 eq77
    | exact resolve eq77 eq32318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq32318
  have eq32448 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq32396
    | exact resolve eq32396 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32396
  have eq35529 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30261 eq56
    | exact resolve eq56 eq30261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35548 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30261 eq3790
    | (have j0 := eq3790 (σ x)
       grind)
    | exact resolve eq3790 eq30261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30261
  have eq35566 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq35548
    | exact resolve eq35548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35548
  have eq35567 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq35566
  have eq35576 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq35529
    | exact resolve eq35529 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35529
  have eq35731 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq35567
  have eq35947 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq35731 eq56
    | exact resolve eq56 eq35731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35731
  have eq36003 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq35947
    | exact resolve eq35947 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35947
  have eq36104 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3790 x
       have i₂ := eq32448
       grind)
    | exact superpose eq32448 eq3790
    | (have j0 := eq3790 x
       grind)
    | exact resolve eq3790 eq32448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790
  have eq36127 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36104
    | exact resolve eq36104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36104
  have eq36128 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq36127
  have eq36180 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq35576
       have i₂ := eq36003
       grind)
    | exact superpose eq36003 eq35576
    | exact resolve eq35576 eq36003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35576 eq36003
  have eq36208 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq36180
  have eq36235 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq36208 eq28
    | exact resolve eq28 eq36208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36208
  have eq44011 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq36128
  have eq45033 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32448
       have i₂ := eq44011
       grind)
    | exact superpose eq44011 eq32448
    | exact resolve eq32448 eq44011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32448 eq44011
  have eq45063 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq45033
  have eq45370 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq45063 eq30
    | exact resolve eq30 eq45063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq45063
  have eq45642 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq45370
    | exact resolve eq45370 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45370
  have eq45643 : x = (M.op x y) ∨ x = y := by grind
  clear eq45642
  have eq45644 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq45643 eq21
    | exact resolve eq21 eq45643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45643
  have eq45869 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq45644
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45644
    | exact resolve eq45644 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45644
  have eq45870 : x = y := by
    first
    | (have r₁ := eq45869
       have r₂ := eq36235
       grind)
    | exact resolve eq45869 eq36235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36235 eq45869
  have eq45871 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq45870
       grind)
    | exact superpose eq45870 eq19
    | exact resolve eq19 eq45870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq45872 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq45870
       grind)
    | exact superpose eq45870 eq25
    | exact resolve eq25 eq45870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq46007 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29961
       have i₂ := eq45870
       grind)
    | exact superpose eq45870 eq29961
    | exact resolve eq29961 eq45870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29961 eq45870
  have eq46102 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq45872
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45872
    | exact resolve eq45872 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45872
  have eq46107 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq46102 eq27
    | exact resolve eq27 eq46102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq46102
  have eq46515 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq50715 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq584 x x
       have i₂ := eq46007
       grind)
    | exact superpose eq46007 eq584
    | (have j0 := eq584 x x
       grind)
    | exact resolve eq584 eq46007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq46007
  have eq50724 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50715
  have eq50725 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50724
  have eq50738 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50725
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq50725
    | exact resolve eq50725 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50725
  have eq50761 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46107 eq50738
    | exact resolve eq50738 eq46107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46107 eq50738
  have eq50762 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50761
  have eq50782 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq50762 eq28
    | exact resolve eq28 eq50762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq50868 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq50762 eq46515
    | exact resolve eq46515 eq50762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46515 eq50762
  have eq51600 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq50868 eq56
    | exact resolve eq56 eq50868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq50868
  have eq51665 : x = (k x x) := by
    first
    | exact superpose eq29 eq51600
    | exact resolve eq51600 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq51600
  have eq51708 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq51665
       grind)
    | exact superpose eq51665 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq51665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51665
  have eq51709 : x = (M.op x x) := by grind
  clear eq51708
  have eq51725 : x = (M.op x y) := by
    first
    | (have i₁ := eq51709
       have i₂ := eq45871
       grind)
    | exact superpose eq45871 eq51709
    | exact resolve eq51709 eq45871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45871 eq51709
  have eq52509 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq51725 eq21
    | exact resolve eq21 eq51725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq51725
  have eq52794 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq52509
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52509
    | exact resolve eq52509 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq52509
  have eq52871 : False := by grind
  exact eq52871

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq37 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq43 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq87 : ∀ X0 : G, (τ (σ X0)) = (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq23
    | exact resolve eq23 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq88 : ∀ X0 : G, (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87
    | exact resolve eq87 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq95 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq9
    | exact resolve eq9 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq106 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 X0)
       have i₂ := eq97 X0 X2
       grind)
    | exact superpose eq97 eq9
    | exact resolve eq9 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq104
    | exact resolve eq104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1 (M.op X0 X0)
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq104
    | exact resolve eq104 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq660 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq137 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq137
    | exact resolve eq137 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 (M.op X0 X1) X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq660
    | exact resolve eq660 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq807 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq772 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq772
    | exact resolve eq772 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq842 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq859 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  clear eq19
  have eq1044 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106 X0 X1 X2
       have i₂ := eq807 X0 X2
       grind)
    | exact superpose eq807 eq106
    | exact resolve eq106 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq1164 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq772 (M.op X2 X1) (M.op X1 (M.op X0 X1))
       have i₂ := eq1044 X1 X2 X0
       grind)
    | exact superpose eq1044 eq772
    | exact resolve eq772 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq1044
  have eq1166 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1164 X0 X1 X2
       have i₂ := eq807 X1 X2
       grind)
    | exact superpose eq807 eq1164
    | exact resolve eq1164 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq1164
  have eq1194 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137 X0 X1 X2
       have i₂ := eq1166 X0 X1 X0
       grind)
    | exact superpose eq1166 eq137
    | exact resolve eq137 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq1166
  have eq18091 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq842 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq842
    | (have j0 := eq842 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq842 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18095 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq18123 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq842 X1 X0
       grind)
    | exact superpose eq842 eq10
    | (have j1 := eq842 X1 X0
       grind)
    | exact resolve eq10 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq18141 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq18095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18095
  have eq20678 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq18141 X0
       grind)
    | exact superpose eq18141 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (σ X0)
       have j1 := eq18141 X0
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have r₂ := eq18141 X0
       grind)
    | exact resolve eq13 eq18141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18141
  have eq20759 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq20678 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20678
  have eq20760 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq20759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759
  have eq20780 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20760 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq20760
    | (have j0 := eq20760 X0
       grind)
    | exact resolve eq20760 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20760
  have eq20795 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq20780
  have eq41290 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20795 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20795
    | exact resolve eq20795 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41304 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq18123 X0 X0
       have i₂ := eq20795 X0
       grind)
    | exact superpose eq20795 eq18123
    | (have j0 := eq18123 X0 X0
       have j1 := eq20795 X0
       grind)
    | exact resolve eq18123 eq20795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123
  have eq41308 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0)
       have i₂ := eq20795 X0
       grind)
    | exact superpose eq20795 eq95
    | (have j1 := eq20795 X0
       grind)
    | exact resolve eq95 eq20795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41423 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq20795 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20795
  have eq41424 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq41304 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41304
  have eq41439 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41424 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq41424
    | (have j0 := eq41424 X0
       grind)
    | exact resolve eq41424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41424
  have eq41446 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41439 X0
       have j1 := eq41423 X0
       grind)
    | (have r₁ := eq41439 X0
       have r₂ := eq41423 X0
       grind)
    | exact resolve eq41439 eq41423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41423 eq41439
  have eq41463 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq41290 X0
       grind)
    | exact superpose eq41290 eq10
    | (have j1 := eq41290 X0
       grind)
    | exact resolve eq10 eq41290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41290
  have eq41580 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq41446 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq41446
    | (have j0 := eq41446 (τ X0)
       grind)
    | exact resolve eq41446 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41594 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq41446 X0
       grind)
    | exact superpose eq41446 eq43
    | (have j1 := eq41446 X0
       grind)
    | exact resolve eq43 eq41446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq41595 : ∀ X0 : G, (k (τ (τ (σ (σ X0)))) X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq41446 (σ X0)
       grind)
    | exact superpose eq41446 eq88
    | (have j1 := eq41446 (σ X0)
       grind)
    | exact resolve eq88 eq41446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq41446
  have eq41756 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41595 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq41595
    | (have j0 := eq41595 X0
       grind)
    | exact resolve eq41595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41595
  have eq41757 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq41594 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41594
    | (have j0 := eq41594 X0
       grind)
    | exact resolve eq41594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41594
  have eq41764 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq41580 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq41580
    | (have j0 := eq41580 X0
       grind)
    | exact resolve eq41580 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41580
  have eq41770 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41756 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41756
    | (have j0 := eq41756 X0
       grind)
    | exact resolve eq41756 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41756
  have eq41775 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq41770 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq41770
    | (have j0 := eq41770 X0
       grind)
    | exact resolve eq41770 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41770
  have eq41807 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq41757 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42223 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq41463 eq41764
    | (have j0 := eq41764 X0
       have j1 := eq41463 X0
       grind)
    | exact resolve eq41764 eq41463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41463 eq41764
  have eq42230 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq42223 X0
       grind)
    | exact superpose eq42223 eq11
    | (have j1 := eq42223 X0
       grind)
    | exact resolve eq11 eq42223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42223
  have eq42273 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq42230 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq42230
    | (have j0 := eq42230 X0
       grind)
    | exact resolve eq42230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42230
  have eq42292 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq42273 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq42273
    | (have j0 := eq42273 (τ X0)
       grind)
    | exact resolve eq42273 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42338 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq41757 eq41775
    | (have j0 := eq41775 X0
       have j1 := eq41757 X0
       grind)
    | exact resolve eq41775 eq41757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41757 eq41775
  have eq42358 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0)
       have i₂ := eq42338 X0
       grind)
    | exact superpose eq42338 eq95
    | (have j1 := eq42338 X0
       grind)
    | exact resolve eq95 eq42338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42338
  have eq42774 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq42358 (τ X0)
       have i₂ := eq859 X0 (τ X0)
       grind)
    | exact superpose eq859 eq42358
    | (have j0 := eq42358 (τ X0)
       have j1 := eq859 X0 (τ X0)
       grind)
    | exact resolve eq42358 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq42358
  have eq42874 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq42774 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42774
  have eq42903 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq42874 X0
       have j1 := eq41807 (τ X0)
       grind)
    | (have r₁ := eq42874 X0
       have r₂ := eq41807 (τ X0)
       grind)
    | exact resolve eq42874 eq41807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41807 eq42874
  have eq42940 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq42903 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42903
    | (have j0 := eq42903 X0
       grind)
    | exact resolve eq42903 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42903
  have eq42960 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq42940 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq42940
    | (have j0 := eq42940 X0
       grind)
    | exact resolve eq42940 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq42940
  have eq52661 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18091 x y
       grind)
    | exact superpose eq18091 eq16
    | (have j1 := eq18091 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq18091 x y
       grind)
    | exact resolve eq16 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18091
  have eq52848 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq52661
  have eq52904 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq41308 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41308
  have eq57257 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq42292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42292
  have eq57337 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq57257 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57257
  have eq57367 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq57337 X0
       have j1 := eq42960 X0
       grind)
    | (have r₁ := eq57337 X0
       have r₂ := eq42960 X0
       grind)
    | exact resolve eq57337 eq42960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42960 eq57337
  have eq57423 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (σ X0) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq57367 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57367
    | (have j0 := eq57367 (σ X0)
       grind)
    | exact resolve eq57367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57367
  have eq57672 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57423 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq57423
    | (have j0 := eq57423 X0
       grind)
    | exact resolve eq57423 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57423
  have eq57694 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq42273 eq57672
    | (have j0 := eq57672 X0
       have j1 := eq42273 X0
       grind)
    | exact resolve eq57672 eq42273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42273 eq57672
  have eq57725 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57694 (M.op x x)
       have i₂ := eq1194 x x x
       grind)
    | exact superpose eq1194 eq57694
    | exact resolve eq57694 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq57694
  have eq57932 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57725 X0
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq57725
    | (have j0 := eq57725 X0
       grind)
    | exact resolve eq57725 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57725
  have eq57967 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57932 X0
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq57932
    | (have j0 := eq57932 X0
       grind)
    | exact resolve eq57932 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57932
  have eq205828 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq95 (σ x)
       have i₂ := eq52848
       grind)
    | exact superpose eq52848 eq95
    | exact resolve eq95 eq52848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52848
  have eq206104 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq205828
  have eq206392 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206104
       grind)
    | exact superpose eq206104 eq16
    | exact resolve eq16 eq206104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206399 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq138 (σ y) (σ x)
       have i₂ := eq206104
       grind)
    | exact superpose eq206104 eq138
    | exact resolve eq138 eq206104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206641 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq206104 eq206399
    | exact resolve eq206399 eq206104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206104 eq206399
  have eq206692 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105 (σ y)
       have i₂ := eq206641
       grind)
    | exact superpose eq206641 eq105
    | exact resolve eq105 eq206641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq206641
  have eq207053 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq206692
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq206692
    | exact resolve eq206692 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206692
  have eq207111 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq207053
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq207053 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207053
  have eq207137 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq207111
       have r₂ := eq206392
       grind)
    | exact resolve eq207111 eq206392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206392 eq207111
  have eq207172 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95 x
       have i₂ := eq207137
       grind)
    | exact superpose eq207137 eq95
    | exact resolve eq95 eq207137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq207137
  have eq207448 : x = (M.op x y) := by grind
  clear eq207172
  have eq207500 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq207448
       grind)
    | exact superpose eq207448 eq16
    | exact resolve eq16 eq207448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207502 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq138 y x
       have i₂ := eq207448
       grind)
    | exact superpose eq207448 eq138
    | exact resolve eq138 eq207448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq207738 : x = (M.op y y) := by
    first
    | (have i₁ := eq207502
       have i₂ := eq207448
       grind)
    | exact superpose eq207448 eq207502
    | exact resolve eq207502 eq207448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207502
  have eq207810 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq57967 y
       have i₂ := eq207738
       grind)
    | exact superpose eq207738 eq57967
    | exact resolve eq57967 eq207738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57967 eq207738
  have eq208050 : x = y := by
    first
    | (have r₁ := eq207810
       have r₂ := eq207500
       grind)
    | exact resolve eq207810 eq207500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207810
  have eq208062 : x = (M.op x x) := by
    first
    | (have i₁ := eq207448
       have i₂ := eq208050
       grind)
    | exact superpose eq208050 eq207448
    | exact resolve eq207448 eq208050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207448
  have eq208063 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq207500
       have i₂ := eq208050
       grind)
    | exact superpose eq208050 eq207500
    | exact resolve eq207500 eq208050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207500 eq208050
  have eq208118 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq52904 x
       have i₂ := eq208062
       grind)
    | exact superpose eq208062 eq52904
    | (have j0 := eq52904 x
       grind)
    | exact resolve eq52904 eq208062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52904 eq208062
  have eq208329 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq208118
  have eq208408 : False := by grind
  exact eq208408

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq9 X1 (M.op x (M.op X1 x)) X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X1) = (k X0 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq125 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq125 X1 X1
       grind)
    | exact superpose eq125 eq13
    | (have j0 := eq13 X0 X2
       have j1 := eq125 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq125 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq125 X1 X1
       grind)
    | exact resolve eq13 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq125 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq125 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq125 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq125 X1 X1
       grind)
    | exact resolve eq13 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq204 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq206 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq204 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq204 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq275 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (k X0 X1)) (k X0 X1)) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq206 X0 X1
       grind)
    | exact superpose eq206 eq9
    | (have j1 := eq206 X0 X1
       grind)
    | exact resolve eq9 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq294 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (M.op X0 X0) X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq40
    | exact resolve eq40 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X2 (M.op X1 X0))) (M.op (M.op X3 X1) (M.op X3 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq29 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X1 X1 X2 (M.op X1 X1)
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq29
    | exact resolve eq29 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X2 (M.op X0 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40 X0 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1))) X3
       have i₂ := eq29 X0 X0 X2 X1
       grind)
    | exact superpose eq29 eq40
    | exact resolve eq40 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40
  have eq1430 : ∀ X1 X2 : G, (M.op X1 X1) = (M.op (M.op X1 X2) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq892 X1 X2 (M.op X1 X2) (M.op x (M.op (M.op X1 X2) x))
       have i₂ := eq9 (M.op X1 X2) x x
       grind)
    | exact superpose eq9 eq892
    | exact resolve eq892 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq1515 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1430 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq1430
    | exact resolve eq1430 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1430
  have eq1627 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq184 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1631 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1627 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1627 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1627 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq3004 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1631 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3855 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq861 X0 X1 X2
       have i₂ := eq1515 X0 X1
       grind)
    | exact superpose eq1515 eq861
    | exact resolve eq861 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq5983 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1 x
       have i₂ := eq294 (k X0 X1) x
       grind)
    | exact superpose eq294 eq275
    | (have j0 := eq275 X0 X1 x
       grind)
    | exact resolve eq275 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq294
  have eq6127 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5983 X1 X0
       have i₂ := eq1631 X0 X1
       grind)
    | exact superpose eq1631 eq5983
    | (have j0 := eq5983 X1 X0
       have j1 := eq1631 X0 X1
       grind)
    | exact resolve eq5983 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631 eq5983
  have eq6268 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq6127 X0 X1
       have j1 := eq3004 X1 X0
       grind)
    | (have r₁ := eq6127 X0 X1
       have r₂ := eq3004 X0 X1
       grind)
    | (have r₁ := eq6127 X1 X0
       have r₂ := eq3004 X0 X1
       grind)
    | exact resolve eq6127 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6127
  have eq6269 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6268 X0 X1
       have i₂ := eq1515 X0 X1
       grind)
    | exact superpose eq1515 eq6268
    | (have j0 := eq6268 X0 X1
       grind)
    | exact resolve eq6268 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6268
  have eq7470 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X2 (M.op X1 X0))) (M.op X1 (M.op X3 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq856 X0 X1 X2 X3 X4
       have i₂ := eq1515 X1 X3
       grind)
    | exact superpose eq1515 eq856
    | exact resolve eq856 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq1515
  have eq7752 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op (M.op X2 X1) (M.op X2 (M.op X3 X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq7470 X1 X2 X1 X3 (M.op x X1)
       have i₂ := eq3855 X1 X2 x
       grind)
    | exact superpose eq3855 eq7470
    | exact resolve eq7470 eq3855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3855 eq7470
  have eq8010 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7752 (M.op X0 X0) X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7752
    | exact resolve eq7752 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7752
  have eq8310 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8010 X0 X1
       have i₂ := eq6269 X0 X1
       grind)
    | exact superpose eq6269 eq8010
    | (have j1 := eq6269 X0 X1
       grind)
    | exact resolve eq8010 eq6269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6269 eq8010
  have eq8400 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq8310 X0 X1
       have j1 := eq3004 X1 X0
       grind)
    | (have r₁ := eq8310 X0 X1
       have r₂ := eq3004 X0 X1
       grind)
    | (have r₁ := eq8310 X1 X0
       have r₂ := eq3004 X0 X1
       grind)
    | exact resolve eq8310 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004 eq8310
  have eq8544 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq8400 (σ X1) (σ X0)
       grind)
    | exact superpose eq8400 eq15
    | exact resolve eq15 eq8400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8557 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8544 X0 X1
       have i₂ := eq8400 X1 X0
       grind)
    | exact superpose eq8400 eq8544
    | exact resolve eq8544 eq8400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8400 eq8544
  have eq8695 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8557 y x
       grind)
    | exact superpose eq8557 eq16
    | (have r₁ := eq16
       have r₂ := eq8557 y x
       grind)
    | exact resolve eq16 eq8557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8557
  have eq8727 : False := by grind
  exact eq8727

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 X0)
       have i₂ := eq64 X0 X2
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq72
    | exact resolve eq72 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq143 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq143 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq143 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq143 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq154 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq147 (σ X0)
       grind)
    | exact superpose eq147 eq15
    | exact resolve eq15 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq147 (τ X0)
       grind)
    | exact superpose eq147 eq31
    | exact resolve eq31 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq156 X0
       have i₂ := eq147 X0
       grind)
    | exact superpose eq147 eq156
    | exact resolve eq156 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq169 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq154 X0
       have i₂ := eq147 X0
       grind)
    | exact superpose eq147 eq154
    | exact resolve eq154 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq154
  have eq226 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq88 (τ X0) (τ X0)
       have i₂ := eq167 X0
       grind)
    | exact superpose eq167 eq88
    | exact resolve eq88 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 : G, (M.op (τ X0) (τ X0)) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq226 X0
       grind)
    | exact superpose eq226 eq13
    | (have j0 := eq13 (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact resolve eq13 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq341 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq335 X0
       grind)
    | (have r₁ := eq335 X0
       have r₂ := eq167 X0
       grind)
    | exact resolve eq335 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq347 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq341 X0
       have i₂ := eq167 X0
       grind)
    | exact superpose eq167 eq341
    | (have j0 := eq341 X0
       grind)
    | exact resolve eq341 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq350 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq347 X0
       have i₂ := eq31 X0 (M.op X0 X0)
       grind)
    | exact superpose eq31 eq347
    | (have j0 := eq347 X0
       grind)
    | exact resolve eq347 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq351 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq350 X0
       have i₂ := eq167 (M.op X0 X0)
       grind)
    | exact superpose eq167 eq350
    | (have j0 := eq350 X0
       grind)
    | exact resolve eq350 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq352 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq351 X0
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq351
    | (have j0 := eq351 X0
       grind)
    | exact resolve eq351 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq657 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq667 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq62 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq726 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq725 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq728 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq724 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq724 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq724 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq737 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq726 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq726 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq726 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq763 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq667 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq667 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq667 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq768 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq169 X1
       grind)
    | exact superpose eq169 eq657
    | (have j0 := eq657 X0 X1
       grind)
    | exact resolve eq657 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq790 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq768 X0 X1
       have i₂ := eq169 X1
       grind)
    | exact superpose eq169 eq768
    | (have j0 := eq768 X0 X1
       grind)
    | exact resolve eq768 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq890 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq737 X1 (σ X0)
       grind)
    | exact superpose eq737 eq28
    | (have j1 := eq737 X1 (σ X0)
       grind)
    | exact resolve eq28 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq907 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq737 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq890 X0 X1
       have i₂ := eq169 X0
       grind)
    | exact superpose eq169 eq890
    | (have j0 := eq890 X0 X1
       grind)
    | exact resolve eq890 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq936 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq920 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq920
    | (have j0 := eq920 X0 X1
       grind)
    | exact resolve eq920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq974 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (M.op (σ X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq763 (σ X0) X1
       grind)
    | exact superpose eq763 eq28
    | (have j1 := eq763 (σ X0) X1
       grind)
    | exact resolve eq28 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq763
  have eq1040 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (k (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq907 (M.op X0 X0) X1
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq907
    | exact resolve eq907 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1040 X0 X0
       have i₂ := eq88 X0 X0
       grind)
    | exact superpose eq88 eq1040
    | (have j0 := eq1040 X0 X0
       grind)
    | exact resolve eq1040 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1215 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1169 (τ X0)
       have i₂ := eq167 X0
       grind)
    | exact superpose eq167 eq1169
    | exact resolve eq1169 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1216 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) ≠ (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1215 X0
       have i₂ := eq31 X0 (M.op X0 X0)
       grind)
    | exact superpose eq31 eq1215
    | (have j0 := eq1215 X0
       grind)
    | exact resolve eq1215 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1218 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq1216 X0
       have j1 := eq352 X0
       grind)
    | (have r₁ := eq1216 X0
       have r₂ := eq352 X0
       grind)
    | exact resolve eq1216 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq1216
  have eq1233 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11 (k (M.op X0 X0) X0)
       have i₂ := eq1218 X0
       grind)
    | exact superpose eq1218 eq11
    | exact resolve eq11 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1254 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1233 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1233
    | exact resolve eq1233 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq2172 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X3 X1) (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X1) X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq70 X1 X3 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2380 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq87
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2406 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X2 X3 X1
       have i₂ := eq87 X1 X2 X0
       grind)
    | (have i₁ := eq70 X1 X1 X1
       have i₂ := eq87 X1 X1 X1
       grind)
    | exact superpose eq87 eq70
    | exact resolve eq70 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2573 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2380 X0 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq62 (M.op X0 X1)
       grind)
    | exact superpose eq62 eq2380
    | exact resolve eq2380 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq2638 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2573 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq2573
    | exact resolve eq2573 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2639 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2573 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq2573
    | exact resolve eq2573 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2642 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2573 (M.op X2 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq70 X1 X2 X0
       grind)
    | exact superpose eq70 eq2573
    | exact resolve eq2573 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq2676 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq2573 X0 X1
       grind)
    | exact superpose eq2573 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq2573 X0 X1
       grind)
    | exact resolve eq13 eq2573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2701 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq2676 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676
  have eq2734 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X0 X1 X2
       have i₂ := eq2639 X1 X0
       grind)
    | exact superpose eq2639 eq87
    | exact resolve eq87 eq2639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq2744 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 (M.op X0 X1)) (M.op X1 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2172 X0 X1 X2 X3
       have i₂ := eq2639 X1 X3
       grind)
    | exact superpose eq2639 eq2172
    | exact resolve eq2172 eq2639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172
  have eq2764 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2642 X0 X1 X2
       have i₂ := eq2639 X1 X2
       grind)
    | exact superpose eq2639 eq2642
    | exact resolve eq2642 eq2639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2642
  have eq2766 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2701 X0 X1
       have i₂ := eq2639 X1 X0
       grind)
    | exact superpose eq2639 eq2701
    | (have j0 := eq2701 X0 X1
       grind)
    | exact resolve eq2701 eq2639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701
  have eq2775 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X0 X3) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq2639 (M.op X0 X3) X2
       grind)
    | exact superpose eq2639 eq61
    | exact resolve eq61 eq2639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq2804 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2638 X0 X1 X2
       have i₂ := eq2639 (M.op X0 X2) X1
       grind)
    | exact superpose eq2639 eq2638
    | exact resolve eq2638 eq2639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638 eq2639
  have eq2842 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2775 X0 X1 X2 X3
       have i₂ := eq2804 X0 X2 X3
       grind)
    | exact superpose eq2804 eq2775
    | exact resolve eq2775 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq3505 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) = (M.op (M.op X3 X1) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2573 (M.op X3 X1) (M.op X1 (M.op X0 (M.op X1 X2)))
       have i₂ := eq2842 X1 X3 X0 X2
       grind)
    | exact superpose eq2842 eq2573
    | exact resolve eq2573 eq2842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3515 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) = (M.op X1 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3505 X0 X1 X2 X3
       have i₂ := eq2764 X3 X1 X3
       grind)
    | exact superpose eq2764 eq3505
    | exact resolve eq3505 eq2764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505
  have eq4354 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2744 X0 X0 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq2744
    | exact resolve eq2744 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744
  have eq4658 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4354 X2 X1
       have i₂ := eq2734 X1 X2 X0
       grind)
    | (have i₁ := eq4354 (M.op X2 X0) X0
       have i₂ := eq2734 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq2734 eq4354
    | exact resolve eq4354 eq2734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq4686 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X3 X1) (M.op X1 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    by_contra hcon
    push Not at hcon
    have f4686_12 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X0 X3)))) := by
      intro X0 X1 X2 X3
      grind
    have f4686_13 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
      intro X0 X1
      grind
    have f4686_22 : (M.op X2 (M.op X0 X1)) ≠ (M.op (M.op X3 X1) (M.op X1 (M.op X2 (M.op X0 X1)))) := by grind
    have f4686_62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X3 X1) (M.op X1 (M.op X2 (M.op X0 X1)))) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f4686_12 X0 X1 X2 (M.op X0 (M.op X1 X0))
         have i₂ := f4686_13 X0 X1
         grind)
      | exact superpose f4686_13 f4686_12
      | exact resolve f4686_12 f4686_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f4686_728 : (M.op X2 (M.op X0 X1)) ≠ (M.op X2 (M.op X0 X1)) := by
      first
      | (have i₁ := f4686_22
         have i₂ := f4686_62 X0 X1 X2 X3
         grind)
      | exact superpose f4686_62 f4686_22
      | (have r₁ := f4686_22
         have r₂ := f4686_62 X0 X1 X2 X3
         grind)
      | exact resolve f4686_22 f4686_62
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f4686_746 : False := by grind
    exact f4686_746
  clear eq2842 eq4354
  have eq8316 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X1) (M.op X5 (M.op X3 X1))) = (M.op (M.op X2 (M.op X0 X1)) (M.op X5 (M.op X3 X1))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq3515 X2 (M.op X3 X1) (M.op (M.op x X0) (M.op X0 X1)) X5
       have i₂ := eq2406 x X0 X1 X3
       grind)
    | exact superpose eq2406 eq3515
    | exact resolve eq3515 eq2406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2406 eq3515
  have eq8591 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X5 (M.op X3 X1))) = (M.op X3 (M.op X5 (M.op X3 X1))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8316 X0 X1 X2 X3 X5
       have i₂ := eq2804 X3 X5 X1
       grind)
    | exact superpose eq2804 eq8316
    | exact resolve eq8316 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804 eq8316
  have eq19628 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (k (M.op X0 X1) X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2573 X1 (M.op X0 X1)
       have i₂ := eq2766 X0 X1
       grind)
    | exact superpose eq2766 eq2573
    | (have j1 := eq2766 X0 X1
       grind)
    | exact resolve eq2573 eq2766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq29361 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq936 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq936
    | (have j0 := eq936 X1 (σ X0)
       grind)
    | exact resolve eq936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq29763 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29361 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq29361
    | (have j0 := eq29361 X0 X1
       grind)
    | exact resolve eq29361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29361
  have eq33553 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29763 X0 X1
       have i₂ := eq737 X0 X1
       grind)
    | exact superpose eq737 eq29763
    | (have j0 := eq29763 X1 X0
       have j1 := eq737 X1 X0
       grind)
    | exact resolve eq29763 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq29763
  have eq34027 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33553 X0 X1
       have j1 := eq907 X0 X1
       grind)
    | (have r₁ := eq33553 X0 X1
       have r₂ := eq907 X0 X1
       grind)
    | (have r₁ := eq33553 X1 X1
       have r₂ := eq907 X1 X1
       grind)
    | exact resolve eq33553 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq33553
  have eq42193 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34027 x y
       grind)
    | exact superpose eq34027 eq16
    | (have j1 := eq34027 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq34027 x y
       grind)
    | exact resolve eq16 eq34027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34027
  have eq42736 : (k x y) = (M.op x x) := by grind
  clear eq42193
  have eq43006 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq790 x y
       have i₂ := eq42736
       grind)
    | exact superpose eq42736 eq790
    | (have j0 := eq790 x y
       grind)
    | exact resolve eq790 eq42736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq51756 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4658 x X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq4686 X1 X2 X0 x
       grind)
    | exact superpose eq4686 eq4658
    | exact resolve eq4658 eq4686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4658 eq4686
  have eq51967 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51756 X0 X1 X2
       have i₂ := eq8591 X1 X2 X0 X1 X0
       grind)
    | exact superpose eq8591 eq51756
    | exact resolve eq51756 eq8591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8591 eq51756
  have eq107375 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq974 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq974
    | exact resolve eq974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq107979 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107375 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq107375
    | (have j0 := eq107375 X0 X1
       grind)
    | exact resolve eq107375 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq107375
  have eq108410 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51967 X1 X0 X1
       have i₂ := eq107979 X0 X1
       grind)
    | exact superpose eq107979 eq51967
    | (have j1 := eq107979 X1 X0
       grind)
    | exact resolve eq51967 eq107979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51967 eq107979
  have eq110628 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq108410 y x
       have i₂ := eq42736
       grind)
    | exact superpose eq42736 eq108410
    | (have j0 := eq108410 y x
       grind)
    | exact resolve eq108410 eq42736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108410
  have eq111788 : (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op x x)) (τ (M.op x x))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq167 (M.op x y)
       have i₂ := eq110628
       grind)
    | exact superpose eq110628 eq167
    | exact resolve eq167 eq110628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110628
  have eq111862 : (τ (M.op (M.op x y) (M.op x y))) = (τ (M.op (M.op x x) (M.op x x))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111788
       have i₂ := eq167 (M.op x x)
       grind)
    | exact superpose eq167 eq111788
    | exact resolve eq111788 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq111788
  have eq111881 : (τ (M.op (M.op x y) (M.op x y))) = (τ (M.op x (M.op x x))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111862
       have i₂ := eq2764 x x x
       grind)
    | exact superpose eq2764 eq111862
    | exact resolve eq111862 eq2764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111862
  have eq111882 : (τ x) = (τ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111881
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq111881
    | exact resolve eq111881 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111881
  have eq111883 : (τ x) = (τ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111882
       have i₂ := eq2764 x y x
       grind)
    | exact superpose eq2764 eq111882
    | exact resolve eq111882 eq2764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764 eq111882
  have eq112600 : (M.op y (M.op x y)) = (σ (τ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 (M.op y (M.op x y))
       have i₂ := eq111883
       grind)
    | exact superpose eq111883 eq11
    | exact resolve eq11 eq111883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111883
  have eq112708 : x = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq112600
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq112600
    | exact resolve eq112600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112600
  have eq112818 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2573 y (M.op x y)
       have i₂ := eq112708
       grind)
    | exact superpose eq112708 eq2573
    | exact resolve eq2573 eq112708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573 eq112708
  have eq112901 : (M.op x y) = (M.op y y) := by grind
  clear eq112818
  have eq112949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq43006
       have i₂ := eq112901
       grind)
    | exact superpose eq112901 eq43006
    | exact resolve eq43006 eq112901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43006
  have eq113049 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq112949
       have r₂ := eq16
       grind)
    | exact resolve eq112949 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112949
  have eq113063 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq113049
       have i₂ := eq112901
       grind)
    | exact superpose eq112901 eq113049
    | exact resolve eq113049 eq112901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113049
  have eq113079 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq112901
       grind)
    | exact superpose eq112901 eq12
    | (have j0 := eq12 X0 y
       grind)
    | exact resolve eq12 eq112901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155866 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq88 (σ y) (σ x)
       have i₂ := eq113063
       grind)
    | exact superpose eq113063 eq88
    | exact resolve eq88 eq113063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq155952 : (M.op (σ y) (σ y)) = (M.op (k (σ (M.op x x)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19628 (σ x) (σ y)
       have i₂ := eq113063
       grind)
    | exact superpose eq113063 eq19628
    | (have j0 := eq19628 (σ x) x
       grind)
    | exact resolve eq19628 eq113063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19628 eq113063
  have eq155995 : (M.op (σ y) (σ y)) = (M.op (σ (k (M.op x x) x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq155952
       have i₂ := eq15 (M.op x x) x
       grind)
    | exact superpose eq15 eq155952
    | exact resolve eq155952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155952
  have eq156045 : (σ (M.op y y)) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq155866
       have i₂ := eq169 y
       grind)
    | exact superpose eq169 eq155866
    | exact resolve eq155866 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155866
  have eq156070 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq155995
       have i₂ := eq1254 x
       grind)
    | exact superpose eq1254 eq155995
    | exact resolve eq155995 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254 eq155995
  have eq156098 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq156045
       have i₂ := eq112901
       grind)
    | exact superpose eq112901 eq156045
    | exact resolve eq156045 eq112901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156045
  have eq156114 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq156070
       have i₂ := eq169 y
       grind)
    | exact superpose eq169 eq156070
    | exact resolve eq156070 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156070
  have eq156134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq156114
       have i₂ := eq112901
       grind)
    | exact superpose eq112901 eq156114
    | exact resolve eq156114 eq112901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112901 eq156114
  have eq156139 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq156134
       have r₂ := eq16
       grind)
    | exact resolve eq156134 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156134
  have eq156142 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq156139
       have i₂ := eq169 x
       grind)
    | exact superpose eq169 eq156139
    | exact resolve eq156139 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156139
  have eq156171 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq156142
       grind)
    | exact superpose eq156142 eq10
    | exact resolve eq10 eq156142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156142
  have eq156261 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq156171
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq156171
    | exact resolve eq156171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156171
  have eq156413 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq156261
       grind)
    | exact superpose eq156261 eq10
    | exact resolve eq10 eq156261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156261
  have eq156503 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq156413
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq156413
    | exact resolve eq156413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156413
  have eq156686 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq728 y x
       have i₂ := eq156503
       grind)
    | exact superpose eq156503 eq728
    | (have r₁ := eq728 y x
       have r₂ := eq156503
       grind)
    | (have r₁ := eq728 x x
       have r₂ := eq156503
       grind)
    | exact resolve eq728 eq156503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq156805 : y = (k x y) ∨ x = (M.op x x) := by grind
  clear eq156686
  have eq156860 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq156805
       have i₂ := eq42736
       grind)
    | exact superpose eq42736 eq156805
    | exact resolve eq156805 eq42736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156805
  have eq156987 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq62 x
       have i₂ := eq156860
       grind)
    | exact superpose eq156860 eq62
    | exact resolve eq62 eq156860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq157196 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq156860
  have eq157353 : x = y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq156503
       have i₂ := eq156987
       grind)
    | exact superpose eq156987 eq156503
    | exact resolve eq156503 eq156987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156503 eq156987
  have eq157494 : x = y ∨ x = (M.op x x) := by grind
  clear eq157353
  have eq157557 : x = (M.op x x) := by
    first
    | (have r₁ := eq157494
       have r₂ := eq157196
       grind)
    | exact resolve eq157494 eq157196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157196 eq157494
  have eq157576 : x = (k x y) := by
    first
    | (have i₁ := eq42736
       have i₂ := eq157557
       grind)
    | exact superpose eq157557 eq42736
    | exact resolve eq42736 eq157557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42736
  have eq158083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq156098
       have i₂ := eq157557
       grind)
    | exact superpose eq157557 eq156098
    | exact resolve eq156098 eq157557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156098
  have eq158134 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq158083
       have r₂ := eq16
       grind)
    | exact resolve eq158083 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158083
  have eq158222 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq158134
       grind)
    | exact superpose eq158134 eq16
    | exact resolve eq16 eq158134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160458 : (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq158134
       grind)
    | exact superpose eq158134 eq10
    | exact resolve eq10 eq158134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158134
  have eq160550 : y = (M.op x y) := by
    first
    | (have i₁ := eq160458
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq160458
    | exact resolve eq160458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160458
  have eq160651 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq113079 X0
       have i₂ := eq160550
       grind)
    | exact superpose eq160550 eq113079
    | (have j0 := eq113079 X0
       grind)
    | (have r₁ := eq113079 X0
       have r₂ := eq160550
       grind)
    | exact resolve eq113079 eq160550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113079
  have eq162857 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq160651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160651
  have eq163697 : x = (M.op x y) := by
    first
    | (have i₁ := eq157576
       have i₂ := eq162857 x
       grind)
    | exact superpose eq162857 eq157576
    | exact resolve eq157576 eq162857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157576 eq162857
  have eq163921 : x = y := by
    first
    | (have i₁ := eq163697
       have i₂ := eq160550
       grind)
    | exact superpose eq160550 eq163697
    | exact resolve eq163697 eq160550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160550 eq163697
  have eq164775 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq158222
       have i₂ := eq163921
       grind)
    | exact superpose eq163921 eq158222
    | exact resolve eq158222 eq163921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158222 eq163921
  have eq167865 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq164775
       have i₂ := eq169 x
       grind)
    | exact superpose eq169 eq164775
    | exact resolve eq164775 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq164775
  have eq168596 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq167865
       have i₂ := eq157557
       grind)
    | exact superpose eq157557 eq167865
    | exact resolve eq167865 eq157557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157557 eq167865
  have eq168597 : False := by grind
  exact eq168597

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq42 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq42 X1 X0
       grind)
    | (have r₁ := eq50 X1 X0
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq50 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq50
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54
  have eq114 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq118 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq114 X0 X1
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq114 X1 X1
       have r₂ := eq56 X1 X1
       grind)
    | exact resolve eq114 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq114
  have eq269 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq118 (σ X0) (σ X1)
       grind)
    | exact superpose eq118 eq15
    | exact resolve eq15 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq269 X0 X1
       have i₂ := eq118 X0 X1
       grind)
    | exact superpose eq118 eq269
    | exact resolve eq269 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq269
  have eq279 : False := by grind
  exact eq279
